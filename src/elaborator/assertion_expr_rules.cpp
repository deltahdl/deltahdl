#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/system_functions.h"
#include "elaborator/assertion_body_slots.h"
#include "elaborator/assertion_rules.h"
#include "elaborator/assertion_walk.h"
#include "elaborator/attached_call_target.h"
#include "elaborator/checker_procedure_rules.h"
#include "elaborator/concurrent_assertion_expr.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/global_clocking_sampled_value.h"
#include "elaborator/procedural_concurrent_assertion.h"
#include "elaborator/property_instance.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "elaborator/sequence_degeneracy.h"
#include "elaborator/sequence_match_attach.h"
#include "elaborator/sequence_match_class.h"
#include "elaborator/typed_sequence_formal.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using NameSet = std::unordered_set<std::string_view>;

enum class Place : uint8_t { kOperand, kDisable, kAbort, kClock };

struct RuleEnv {
  const ScopeMap& params;
  const PropertyRegistry& registry;
  const std::unordered_map<std::string_view, const ModuleItem*>& sequences;
  const std::unordered_map<std::string_view, const ModuleItem*>& subroutines;
  const RtlirModule* mod;
  const ModuleInUnit& scope;
  DiagEngine& diag;
};

struct Site {
  Place place = Place::kOperand;
  const NameSet* locals = nullptr;
  const NameSet* automatics = nullptr;
  bool in_assertion = true;
};

bool IsSampledValueFunction(const Expr* e) {
  if (e->kind != ExprKind::kSystemCall) return false;
  std::string_view n = e->callee;
  return n == "$sampled" || n == "$rose" || n == "$fell" || n == "$stable" ||
         n == "$changed" || n == "$past";
}

bool ReadsMatched(const Expr* e) {
  if (e == nullptr) return false;
  if (SequenceMethodOf(e) == "matched") return true;
  return AnyExprChild(e, [](const Expr* child) { return ReadsMatched(child); });
}

bool MentionsAny(const Expr* e, const NameSet* names) {
  return names != nullptr && !names->empty() && ExprMentionsAny(e, *names);
}

void CheckSampledArguments(const Expr* call, const Site& site,
                           DiagEngine& diag) {
  for (const Expr* arg : call->args) {
    if (MentionsAny(arg, site.locals) || ReadsMatched(arg)) {
      diag.Error(call->range.start,
                 "the arguments of " + std::string(call->callee) +
                     " may not reference a local variable or the sequence "
                     "method matched",
                 Subclause("16.9.3"));
      return;
    }
  }
}

void CheckPastTicks(const Expr* call, const RuleEnv& env) {
  if (call->callee != "$past" || call->args.size() < 2 ||
      call->args[1] == nullptr) {
    return;
  }
  std::optional<int64_t> ticks = ConstEvalInt(call->args[1], env.params);
  if (!ticks.has_value()) {
    env.diag.Error(call->args[1]->range.start,
                   "the number_of_ticks of $past shall be an "
                   "elaboration-time constant expression",
                   Subclause("16.9.3"));
  } else if (*ticks < 1) {
    env.diag.Error(call->args[1]->range.start,
                   "the number_of_ticks of $past shall be 1 or greater",
                   Subclause("16.9.3"));
  }
}

void CheckSampledAutomatics(const Expr* call, const Site& site,
                            DiagEngine& diag) {
  if (site.automatics == nullptr) return;
  bool in_gate = call->callee == "$past" && call->args.size() > 2 &&
                 ExprMentionsAny(call->args[2], *site.automatics);
  bool in_clock = call->sampled_clock != nullptr &&
                  EventsMention(*call->sampled_clock, *site.automatics);
  if (!in_gate && !in_clock) return;
  diag.Error(call->range.start,
             "an automatic variable may not stand in the clocking event or "
             "the expression2 of " +
                 std::string(call->callee),
             Subclause("16.9.3"));
}

void CheckSampledClock(const Expr* call, const Site& site, DiagEngine& diag) {
  if (site.place == Place::kOperand || call->callee == "$sampled" ||
      call->sampled_clock != nullptr) {
    return;
  }
  bool abort = site.place == Place::kAbort;
  diag.Error(call->range.start,
             std::string(call->callee) +
                 (abort ? " in an abort condition"
                        : " in a disable condition or a clocking event") +
                 " shall have its clocking event specified explicitly",
             Subclause(abort ? "16.12.14" : "16.9.3"));
}

void CheckDisableTriggered(const Expr* e, const RuleEnv& env) {
  const ModuleItem* seq = InstantiatedDecl(e->lhs, env.sequences);
  if (seq == nullptr || !seq->seq_clock.empty()) return;
  env.diag.Error(e->range.start,
                 "triggered of the sequence '" + std::string(seq->name) +
                     "', which has no explicit clocking event, may not stand "
                     "in a disable condition",
                 Subclause("16.13.6"));
}

void CheckAbortCondition(const Expr* root, const Site& site, DiagEngine& diag) {
  bool method = false;
  std::vector<const Expr*> stack{root};
  while (!stack.empty()) {
    const Expr* e = stack.back();
    stack.pop_back();
    if (e == nullptr) continue;
    method = method || !SequenceMethodOf(e).empty();
    ForEachExprChild(e, [&](const Expr* child) { stack.push_back(child); });
  }
  if (!method && !MentionsAny(root, site.locals)) return;
  diag.Error(root->range.start,
             "an abort condition may not reference a local variable or the "
             "sequence methods triggered and matched",
             Subclause("16.12.14"));
}

void CheckLocalActuals(const Expr* call, const ModuleItem* seq,
                       const Site& site, const RuleEnv& env) {
  std::vector<Direction> dirs = LocalFormalDirections(seq);
  NameSet bound;
  bool outward = false;
  size_t written = std::min(dirs.size(), call->args.size());
  for (size_t i = 0; i < written; ++i) {
    if (!IsOutward(dirs[i])) continue;
    outward = true;
    const Expr* actual = call->args[i];
    if (!IsLocalRef(actual, *site.locals)) {
      env.diag.Error(call->range.start,
                     "the actual of the inout or output local variable formal "
                     "'" +
                         std::string(seq->prop_formals[i]) + "' of '" +
                         std::string(seq->name) +
                         "' shall be a reference to a local variable in scope",
                     Subclause("16.8.2"));
    } else if (!bound.insert(actual->text).second) {
      env.diag.Error(call->range.start,
                     "the local variable '" + std::string(actual->text) +
                         "' is the actual of two inout or output local "
                         "variable formals of '" +
                         std::string(seq->name) + "'",
                     Subclause("16.8.2"));
    }
  }
  if (outward &&
      AdmitsAnyEmptyMatch(ClassifySequenceMatches(seq, env.registry))) {
    env.diag.Error(call->range.start,
                   "'" + std::string(seq->name) +
                       "', which has an inout or output local variable formal "
                       "argument, admits an empty match",
                   Subclause("16.8.2"));
  }
}

void CheckLocalFormalsOfMethod(const Expr* e, const ModuleItem* seq,
                               const RuleEnv& env) {
  for (Direction dir : LocalFormalDirections(seq)) {
    if (dir == Direction::kNone || dir == Direction::kOutput) continue;
    env.diag.Error(e->range.start,
                   std::string(SequenceMethodOf(e)) +
                       " may not be applied to an instance of '" +
                       std::string(seq->name) +
                       "', which has an input or inout local variable formal "
                       "argument",
                   Subclause("16.8.2"));
    return;
  }
}

void CheckLocalsInMethodActuals(const Expr* e, const Site& site,
                                const RuleEnv& env) {
  for (const Expr* arg : e->lhs->args) {
    if (!MentionsAny(arg, site.locals) || arg->kind == ExprKind::kIdentifier) {
      continue;
    }
    bool matched = SequenceMethodOf(e) == "matched";
    env.diag.Error(arg->range.start,
                   "a local variable passed to an instance that " +
                       std::string(SequenceMethodOf(e)) +
                       " is applied to shall be an entire actual argument",
                   Subclause(matched ? "16.13.5" : "16.10"));
  }
}

void CheckMethodContext(const Expr* e, const ModuleItem* seq, const Site& site,
                        const RuleEnv& env) {
  bool matched = SequenceMethodOf(e) == "matched";
  bool in_sequence = site.in_assertion && site.place == Place::kOperand;
  if (matched && !in_sequence) {
    env.diag.Error(e->range.start,
                   "matched may be used only in a sequence expression",
                   Subclause("16.13.6"));
  }
  if (matched || site.in_assertion || seq == nullptr) return;
  bool assigns = false;
  for (std::string_view formal : seq->prop_formals) {
    if (BodyAssigns(seq->seq_linear, formal)) assigns = true;
  }
  if (!assigns) return;
  env.diag.Error(e->range.start,
                 "triggered may not be applied outside a sequence expression "
                 "to '" +
                     std::string(seq->name) +
                     "', which assigns a formal argument in a match item",
                 Subclause("16.13.6"));
}

void CheckRemovedEndedMethod(const Expr* e, const RuleEnv& env) {
  if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution ||
      e->rhs->text != "ended") {
    return;
  }
  const ModuleItem* seq = InstantiatedDecl(e->lhs, env.sequences);
  if (seq == nullptr) return;
  env.diag.Error(e->range.start,
                 "the ended sequence method has been removed; use the "
                 "triggered method to detect the end point of sequence '" +
                     std::string(seq->name) + "'",
                 Subclause("C.2.3"));
}

void CheckMethodOperand(const Expr* e, const Site& site, const RuleEnv& env) {
  const ModuleItem* seq = InstantiatedDecl(e->lhs, env.sequences);
  CheckMethodContext(e, seq, site, env);
  if (seq == nullptr) return;
  CheckLocalFormalsOfMethod(e, seq, env);
  CheckLocalsInMethodActuals(e, site, env);
}

bool IsFutureGclkCall(const Expr* e) {
  GlobalClockingSampledFunction fn{};
  return ClassifyGlobalClockingSampledFunction(e->callee, fn) &&
         IsGlobalClockingFutureFunction(fn);
}

void CheckFutureGclkNesting(const Expr* call, DiagEngine& diag) {
  bool nested = false;
  for (const Expr* arg : call->args) {
    if (AnySubExpr(arg, IsFutureGclkCall)) nested = true;
  }
  if (GlobalClockingFutureFunctionNestingAllowed(nested)) return;
  diag.Error(call->range.start,
             "a global clocking future sampled value function may not stand "
             "in the argument of " +
                 std::string(call->callee),
             Subclause("16.9.4"));
}

void CheckAssertionFunctionCall(const Expr* call, const RuleEnv& env) {
  auto it = env.subroutines.find(call->callee);
  if (it == env.subroutines.end()) return;
  const ModuleItem* fn = it->second;
  if (HasArgumentWrittenBack(fn)) {
    env.diag.Error(call->range.start,
                   "function '" + std::string(fn->name) +
                       "' has an output, inout or ref argument and cannot be "
                       "called in a concurrent assertion",
                   Subclause("16.6"));
  }
  if (!FunctionIsImpure(fn)) return;
  env.diag.Error(call->range.start,
                 "function '" + std::string(fn->name) +
                     "' keeps state or has a side effect and cannot be called "
                     "in a concurrent assertion",
                 Subclause("16.6"));
}

void CheckIncOrDec(const Expr* e, DiagEngine& diag) {
  bool inc_or_dec =
      (e->kind == ExprKind::kUnary || e->kind == ExprKind::kPostfixUnary) &&
      (e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus);
  if (!inc_or_dec) return;
  diag.Error(e->range.start,
             "an increment or decrement in a concurrent assertion expression "
             "is a side effect, allowed only in a sequence match item "
             "assigning a local variable",
             Subclause("16.6"));
}

void CheckTree(const PropertyExprNode* node, const Site& site,
               const RuleEnv& env);

void CheckSubexpressions(const Expr* e, const Site& site, const RuleEnv& env) {
  if (e == nullptr) return;
  CheckTree(e->property_actual, site, env);
  if (IsSampledValueFunction(e)) {
    CheckSampledArguments(e, site, env.diag);
    CheckPastTicks(e, env);
    CheckSampledAutomatics(e, site, env.diag);
    CheckSampledClock(e, site, env.diag);
  }
  if (site.place == Place::kDisable && SequenceMethodOf(e) == "triggered") {
    CheckDisableTriggered(e, env);
  }
  if (!SequenceMethodOf(e).empty()) CheckMethodOperand(e, site, env);
  CheckRemovedEndedMethod(e, env);
  if (IsFutureGclkCall(e)) CheckFutureGclkNesting(e, env.diag);
  if (e->kind == ExprKind::kCall) {
    const ModuleItem* seq = InstantiatedDecl(e, env.sequences);
    if (seq != nullptr) CheckLocalActuals(e, seq, site, env);
    if (site.in_assertion) CheckAssertionFunctionCall(e, env);
  }
  if (site.in_assertion) CheckIncOrDec(e, env.diag);
  ForEachExprChild(
      e, [&](const Expr* child) { CheckSubexpressions(child, site, env); });
}

void CheckRoot(const Expr* root, const Site& site, const RuleEnv& env) {
  if (root == nullptr) return;
  if (site.place == Place::kAbort) CheckAbortCondition(root, site, env.diag);
  CheckSubexpressions(root, site, env);
}

void CheckClock(const std::vector<EventExpr>& clock, const Site& site,
                const RuleEnv& env) {
  Site at = site;
  at.place = Place::kClock;
  for (const EventExpr& ev : clock) {
    CheckRoot(ev.signal, at, env);
    CheckRoot(ev.iff_condition, at, env);
  }
}

SubroutineArgPassing PassingOf(const FunctionArg& arg) {
  switch (arg.direction) {
    case Direction::kRef:
      return arg.is_const ? SubroutineArgPassing::kByConstRef
                          : SubroutineArgPassing::kByRef;
    case Direction::kOutput:
      return SubroutineArgPassing::kCopiedOut;
    case Direction::kInout:
      return SubroutineArgPassing::kCopiedInOut;
    default:
      return SubroutineArgPassing::kByValueInput;
  }
}

void ReportAttachedArg(std::string_view callee, const Expr* arg,
                       std::string_view what, const RuleEnv& env) {
  env.diag.Error(arg->range.start,
                 std::string(what) + ", in the call of '" +
                     std::string(callee) + "' attached to a sequence",
                 Subclause("16.11"));
}

constexpr std::string_view kAttachedResultUnread =
    "a sequence receives nothing back from a call attached to it";

void CheckAttachedCall(const Expr* call, const Site& site, const RuleEnv& env) {
  const ModuleItem* target = AttachedCallTarget(*call, env.scope);
  if (target == nullptr) return;
  if (ReturnsAValue(target)) {
    WarnDiscardedReturn(call->range.start, target->name, kAttachedResultUnread,
                        env.diag);
  }
  const std::vector<FunctionArg>& formals = target->func_args;
  size_t written = std::min(formals.size(), call->args.size());
  for (size_t i = 0; i < written; ++i) {
    const Expr* arg = call->args[i];
    SubroutineArgPassing passing = PassingOf(formals[i]);
    if (!IsArgPassingAllowedForAttachedCall(passing)) {
      ReportAttachedArg(target->name, arg,
                        "an actual shall be passed by value as an input or by "
                        "reference, which an output or inout formal does not",
                        env);
      continue;
    }
    if (!IsLocalVarArgPassingLegal(MentionsAny(arg, site.locals), passing)) {
      ReportAttachedArg(target->name, arg,
                        "an actual holding a local variable shall be passed "
                        "by value",
                        env);
    }
    if (!IsAutomaticArgUseAllowed(passing, site.automatics != nullptr, true) &&
        MentionsAny(arg, site.automatics)) {
      ReportAttachedArg(target->name, arg,
                        "an automatic variable may not be passed by reference",
                        env);
    }
    if (passing == SubroutineArgPassing::kByValueInput &&
        !IsByValueInputArgumentTypeAllowed(
            ConcurrentAssertionExprReferencedChandle(arg, env.mod).empty())) {
      ReportAttachedArg(target->name, arg,
                        "a variable passed by value shall be of a type an "
                        "assertion may use, which chandle is not",
                        env);
    }
  }
}

void CheckEmptyMatchItems(const std::vector<SeqMatchAssign>& items,
                          SourceLoc loc, DiagEngine& diag) {
  for (bool call : {false, true}) {
    for (const SeqMatchAssign& item : items) {
      if (!item.on_empty_match || (item.call != nullptr) != call) continue;
      diag.Error(loc,
                 std::string(call ? "a subroutine call"
                                  : "a local variable assignment") +
                     " may not be attached to a sequence that admits an "
                     "empty match",
                 Subclause(call ? "16.11" : "16.10"));
      break;
    }
  }
}

void CheckMatchItems(const std::vector<SeqMatchAssign>& items, const Site& site,
                     const RuleEnv& env) {
  for (const SeqMatchAssign& item : items) {
    CheckRoot(item.rhs, site, env);
    if (item.target != nullptr &&
        !SelectPathIsConstant(item.target, env.params)) {
      env.diag.Error(
          item.target->range.start,
          "a sequence match item assigns through a select that is not constant",
          Subclause("A.8.5"));
    }
    if (item.call == nullptr) continue;
    for (const Expr* arg : item.call->args) CheckRoot(arg, site, env);
    if (item.call->kind == ExprKind::kCall) {
      CheckAttachedCall(item.call, site, env);
    } else if (IsStandardSystemFunction(item.call->callee)) {
      WarnDiscardedReturn(item.call->range.start, item.call->callee,
                          kAttachedResultUnread, env.diag);
    }
  }
}

void CheckBody(const SeqLinearBody& body, const Site& site,
               const RuleEnv& env) {
  for (size_t i = 0; i < body.operands.size(); ++i) {
    CheckRoot(body.operands[i], site, env);
    CheckEmptyMatchItems(body.match_items[i], body.operands[i]->range.start,
                         env.diag);
  }
  for (const auto& items : body.match_items) CheckMatchItems(items, site, env);
  CheckMatchItems(body.first_match_items, site, env);
  for (const SeqThroughout& guard : body.throughouts) {
    CheckRoot(guard.cond, site, env);
  }
  for (const auto& clock : body.clocks) CheckClock(clock, site, env);
  CheckClock(body.clock_out, site, env);
  for (const SeqLinearBody& inner : body.intersects) {
    CheckBody(inner, site, env);
  }
  for (const SeqLinearBody& inner : body.conjuncts) CheckBody(inner, site, env);
  for (const SeqLinearBody& inner : body.alternatives) {
    CheckBody(inner, site, env);
  }
}

void CheckSequence(const ModuleItem* seq, const Site& site,
                   const RuleEnv& env) {
  if (seq == nullptr) return;
  CheckBody(seq->seq_linear, site, env);
  CheckClock(seq->seq_clock, site, env);
}

void CheckTree(const PropertyExprNode* node, const Site& site,
               const RuleEnv& env) {
  if (node == nullptr) return;
  Site at = site;
  if (node->kind == PropertyExprNode::Kind::kAbort) at.place = Place::kAbort;
  CheckRoot(node->boolean, at, env);
  for (const auto& values : node->case_values) {
    for (const Expr* value : values) CheckRoot(value, site, env);
  }
  CheckClock(node->clock, site, env);
  CheckSequence(node->sequence, site, env);
  for (const PropertyExprNode* operand : node->operands) {
    CheckTree(operand, site, env);
  }
}

NameSet DeclLocals(const ModuleItem* decl) {
  NameSet locals;
  CollectBodyLocals(decl->seq_linear, locals);
  if (decl->prop_body_tree != nullptr) {
    CollectTreeLocals(decl->prop_body_tree, locals);
  }
  for (const SeqLocalDecl& local : decl->prop_locals) locals.insert(local.name);
  locals.insert(decl->prop_seq_assert_vars.begin(),
                decl->prop_seq_assert_vars.end());
  for (size_t i = 0; i < decl->prop_formals.size(); ++i) {
    if (decl->prop_formal_is_local[i]) locals.insert(decl->prop_formals[i]);
  }
  return locals;
}

bool AssignedOnEveryMatch(const SeqLinearBody& body, std::string_view name,
                          const RuleEnv& env);

bool InstanceAssigns(const Expr* operand, std::string_view name,
                     const RuleEnv& env) {
  const ModuleItem* seq = InstantiatedDecl(operand, env.sequences);
  if (seq == nullptr) return false;
  std::vector<Direction> dirs = LocalFormalDirections(seq);
  size_t written = std::min(dirs.size(), operand->args.size());
  for (size_t j = 0; j < written; ++j) {
    if (IsOutward(dirs[j]) && IsNameRef(operand->args[j], name)) return true;
  }
  return false;
}

bool OperandAssigns(const SeqLinearBody& body, size_t i, std::string_view name,
                    const RuleEnv& env) {
  if (RepeatedFromZero(body, i)) return false;
  return ItemsAssign(body.match_items[i], name) ||
         InstanceAssigns(body.operands[i], name, env);
}

bool AssignedOnEveryMatch(const SeqLinearBody& body, std::string_view name,
                          const RuleEnv& env) {
  bool assigned = ItemsAssign(body.first_match_items, name);
  for (size_t i = 0; i < body.operands.size() && !assigned; ++i) {
    assigned = OperandAssigns(body, i, name, env);
  }
  for (const auto* joined : {&body.conjuncts, &body.intersects}) {
    for (const SeqLinearBody& inner : *joined) {
      assigned = assigned || AssignedOnEveryMatch(inner, name, env);
    }
  }
  if (!assigned) return false;
  for (const SeqLinearBody& alternative : body.alternatives) {
    if (!AssignedOnEveryMatch(alternative, name, env)) return false;
  }
  return true;
}

void CheckOutputsAssigned(const ModuleItem* seq, const RuleEnv& env) {
  if (seq->kind != ModuleItemKind::kSequenceDecl ||
      seq->seq_linear.operands.empty()) {
    return;
  }
  std::vector<Direction> dirs = LocalFormalDirections(seq);
  for (size_t i = 0; i < dirs.size(); ++i) {
    if (dirs[i] != Direction::kOutput ||
        AssignedOnEveryMatch(seq->seq_linear, seq->prop_formals[i], env)) {
      continue;
    }
    env.diag.Error(seq->loc,
                   "the output local variable formal argument '" +
                       std::string(seq->prop_formals[i]) + "' of '" +
                       std::string(seq->name) +
                       "' is unassigned at the completion of a match",
                   Subclause("16.8.2"));
  }
}

void CheckDeclaration(const ModuleItem* decl, const RuleEnv& env) {
  CheckOutputsAssigned(decl, env);
  CheckTypedFormalReferences(decl, env.diag);
  const NameSet kLocals = DeclLocals(decl);
  Site site{Place::kOperand, &kLocals, nullptr};
  CheckSequence(decl, site, env);
  CheckTree(decl->prop_body_tree, site, env);
  CheckClock(decl->prop_clock, site, env);
  Site disable = site;
  disable.place = Place::kDisable;
  CheckRoot(decl->prop_disable_iff, disable, env);
}

void CheckAssertionStmt(const Stmt* s, const NameSet* automatics,
                        const RuleEnv& env) {
  NameSet locals;
  if (s->assert_property != nullptr) {
    CollectTreeLocals(s->assert_property, locals);
  }
  if (s->assert_sequence != nullptr) {
    CollectBodyLocals(s->assert_sequence->seq_linear, locals);
  }
  Site site{Place::kOperand, &locals, automatics};
  if (s->assert_property == nullptr && s->assert_sequence == nullptr) {
    CheckRoot(s->assert_expr, site, env);
  }
  CheckTree(s->assert_property, site, env);
  CheckSequence(s->assert_sequence, site, env);
  CheckClock(s->assert_clock, site, env);
  Site disable = site;
  disable.place = Place::kDisable;
  CheckRoot(s->assert_disable_iff, disable, env);
}

void CheckUnclockedCall(const Expr* e, const RuleEnv& env) {
  if (e == nullptr) return;
  if (IsSampledValueFunction(e) && e->callee != "$sampled" &&
      e->sampled_clock == nullptr) {
    env.diag.Error(e->range.start,
                   std::string(e->callee) +
                       " has no clocking event: none is written, none is "
                       "inferred from the procedure and no default clocking "
                       "is in scope",
                   Subclause("16.9.3"));
  }
  ForEachExprChild(e,
                   [&](const Expr* child) { CheckUnclockedCall(child, env); });
}

void CheckProcedure(const ModuleItem* item, const RtlirModule* mod,
                    const RuleEnv& env) {
  std::vector<const Stmt*> bodies(item->func_body_stmts.begin(),
                                  item->func_body_stmts.end());
  if (IsProceduralItemKind(item->kind)) bodies.push_back(item->body);
  if (bodies.empty()) return;
  const NameSet kAutomatics = CollectItemAutomaticVarNames(item);
  NameSet none;
  Site procedural{Place::kOperand, &none, &kAutomatics, false};
  std::unordered_set<const Expr*> assertion_exprs;
  ForEachProceduralStmt(item, [&](const Stmt* s) {
    if (!s->is_procedural_concurrent) return;
    assertion_exprs.insert(s->assert_expr);
    CheckAssertionStmt(s, &kAutomatics, env);
  });
  bool unclocked = !IsProceduralItemKind(item->kind) ||
                   InferredInProcedure(item, mod).clock.empty();
  bool no_clock = unclocked && DefaultClockingEvent(mod).empty();
  auto visit = [&](const Expr* e) {
    if (e == nullptr || assertion_exprs.count(e) != 0) return;
    CheckSubexpressions(e, procedural, env);
    if (no_clock) CheckUnclockedCall(e, env);
  };
  for (const Stmt* body : bodies) ForEachStmtReadExpr(body, visit);
  ForEachProceduralStmt(item, [&](const Stmt* s) {
    if (s->kind == StmtKind::kWait) visit(s->condition);
  });
}

void CheckContinuousAssign(const ModuleItem* item, const RuleEnv& env) {
  if (item->kind != ModuleItemKind::kContAssign) return;
  for (const Expr* side : {item->assign_lhs, item->assign_rhs}) {
    ForEachSubExpr(side,
                   [&env](const Expr* e) { CheckRemovedEndedMethod(e, env); });
  }
}

}  // namespace

void ValidateAssertionExprRules(const ModuleInUnit& scope,
                                const RtlirModule* mod, const ScopeMap& params,
                                const PropertyRegistry& registry,
                                DiagEngine& diag) {
  const ModuleDecl* decl = &scope.decl;
  const std::unordered_map<std::string_view, const ModuleItem*> kSequences =
      NamedDeclsByName(decl, false);
  std::unordered_map<std::string_view, const ModuleItem*> subroutines;
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      subroutines[item->name] = item;
    }
  }
  const RuleEnv kEnv{params, registry, kSequences, subroutines,
                     mod,    scope,    diag};
  NameSet none;
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl ||
        item->kind == ModuleItemKind::kPropertyDecl) {
      CheckDeclaration(item, kEnv);
    }
    if (item->kind == ModuleItemKind::kDefaultDisableIff) {
      CheckRoot(item->init_expr, Site{Place::kDisable, &none, nullptr}, kEnv);
    }
    if (item->body != nullptr && item->body->is_concurrent_clocked &&
        !IsProceduralItemKind(item->kind)) {
      CheckAssertionStmt(item->body, nullptr, kEnv);
    }
    CheckProcedure(item, mod, kEnv);
    CheckContinuousAssign(item, kEnv);
  }
}

}  // namespace delta
