#include <cmath>
#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/global_clocking_sampled_value.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

namespace {
// Predicate that decides whether an expression targets a writable clockvar.
using ClockvarPredicate = std::function<bool(const Expr*)>;
// Predicate that decides whether a name is an output/inout clockvar signal.
using OutputClockvarNamePredicate = std::function<bool(std::string_view)>;
}  // namespace

// §14.5: an expression bound to a clocking output (or inout) signal forwards to
// a module output port, so it must be a legal output-port connection — that is,
// an assignable target. Assignable forms are a simple name, a hierarchical
// reference, a bit/part-select of one, or a concatenation of such targets.
// Non-assignable forms (literals, operator expressions, calls, replications)
// cannot drive an output port and are therefore rejected. Inputs impose no such
// restriction, since any readable expression is a valid input-port connection.
static bool IsLegalClockingOutputExpr(const Expr* e) {
  if (e == nullptr) return false;
  switch (e->kind) {
    case ExprKind::kIdentifier:
    case ExprKind::kMemberAccess:
      return true;
    case ExprKind::kSelect:
      return IsLegalClockingOutputExpr(e->base);
    case ExprKind::kConcatenation: {
      if (e->elements.empty()) return false;
      for (const Expr* el : e->elements) {
        if (!IsLegalClockingOutputExpr(el)) return false;
      }
      return true;
    }
    default:
      return false;
  }
}

namespace {

// §14.5: a hierarchical expression bound to a clocking output or inout signal
// must be a legal output-port connection (an assignable target); inputs are
// not.
void CheckClockingOutputBinding(const ClockingSignalDecl& sig,
                                DiagEngine& diag) {
  if (sig.hier_expr != nullptr &&
      (sig.direction == Direction::kOutput ||
       sig.direction == Direction::kInout) &&
      !IsLegalClockingOutputExpr(sig.hier_expr)) {
    diag.Error(
        sig.hier_expr->range.start,
        std::format("clocking {} signal '{}' is bound to an expression that "
                    "is not a legal output-port connection",
                    sig.direction == Direction::kInout ? "inout" : "output",
                    sig.name),
        Subclause("14.5"));
  }
}

}  // namespace

// §14.3: the skew a report names for a clocking signal reads the signal's
// direction rather than the field the skew was parsed into.
// Parser::ParseClockingDirection in src/parser/parser_clocking.cpp parses an
// output-only signal's one skew into `in_delay`, and MakeClockingSignal in the
// same file stores that in ClockingSignalDecl::skew_delay and leaves
// out_skew_delay null, so `output #P a;` arrives in the input slot and would
// otherwise be reported as an input skew.
static std::string ClockingSignalSkewRole(const ClockingSignalDecl& sig,
                                          bool from_out_field) {
  std::string_view half =
      (from_out_field || sig.direction == Direction::kOutput) ? "output"
                                                              : "input";
  return std::format("{} skew of clocking signal '{}'", half, sig.name);
}

// §14.3's sentence names one requirement with two ways to break it, and a
// clocking block carries up to four skews, two of which are routinely written
// on one line. So the report names which skew it read, which half of the
// requirement broke, and the value that broke it. `role` is what the caller
// knows and this function does not.
static std::string ClockingSkewMessage(std::string_view role,
                                       std::string_view breach,
                                       std::string_view value) {
  return std::format(
      "{} is {} ({}); a clocking skew shall be a non-negative integer value",
      role, breach, value);
}

// §14.3: a skew that folded to neither an integer nor a time literal. A real
// value that is negative or has a fractional part breaks the non-negative
// integer requirement. An unfoldable-yet-constant form (e.g. a constant
// function call) yields no value here and is left for its own evaluation to
// resolve.
static void CheckClockingSkewRealValue(const Expr* delay,
                                       const ScopeMap& skew_scope,
                                       std::string_view role,
                                       DiagEngine& diag) {
  std::optional<double> rv = ConstEvalReal(delay, skew_scope);
  if (!rv.has_value()) return;
  // The sign is reported before the fractional part, so a skew that breaks both
  // -- `#-1.5` -- still draws one report. An author reading it fixes the sign
  // first, and two reports for one skew would be worse than one.
  if (*rv < 0.0) {
    diag.Error(delay->range.start,
               ClockingSkewMessage(role, "negative", std::format("{}", *rv)),
               Subclause("14.3"));
    return;
  }
  if (*rv != std::floor(*rv)) {
    diag.Error(
        delay->range.start,
        ClockingSkewMessage(role, "not an integer", std::format("{}", *rv)),
        Subclause("14.3"));
  }
}

// §14.4: a clocking skew shall be a constant expression; a parameter is an
// acceptable form. Any skew delay that cannot be folded against the module's
// parameter scope (e.g. a reference to a net or variable) violates the rule.
// §14.3: a skew delay_control is either a time literal or a constant expression
// that evaluates to a non-negative integer value. A time literal is inherently
// a non-negative time value and may be fractional (e.g. a step-scaled delay),
// so it is exempt from the integer requirement. The 1step pseudo-literal folds
// to 0 and is accepted.
static void CheckClockingSkew(const Expr* delay, const ScopeMap& skew_scope,
                              std::string_view role, DiagEngine& diag) {
  if (delay == nullptr) return;
  if (delay->kind == ExprKind::kTimeLiteral) return;
  if (!IsConstantExpr(delay, skew_scope)) {
    diag.Error(delay->range.start,
               "clocking skew shall be a constant expression",
               Subclause("14.4"));
    return;
  }
  std::optional<int64_t> iv = ConstEvalInt(delay, skew_scope);
  if (iv.has_value()) {
    if (*iv < 0) {
      diag.Error(delay->range.start,
                 ClockingSkewMessage(role, "negative", std::format("{}", *iv)),
                 Subclause("14.3"));
    }
    return;
  }
  CheckClockingSkewRealValue(delay, skew_scope, role, diag);
}

void Elaborator::ValidateClockingBlock(ModuleItem* item,
                                       const RtlirModule* mod) {
  // §14.3: only an actual clocking_declaration is subject to the naming rule;
  // an inline clocking event in a property/sequence/assert item is not a
  // clocking block and is reached here only because it shares the item carrier.
  // §14.3/§14.14: a clocking block must be named unless it is the default
  // clocking or a global clocking, both of which may be anonymous.
  if (item->kind == ModuleItemKind::kClockingBlock && item->name.empty() &&
      !item->is_default_clocking && !item->is_global_clocking) {
    diag_.Error(item->loc, "non-default clocking block must have a name",
                Subclause("14.3"));
  }

  // §14.4: a clocking skew shall be a constant expression; a parameter is an
  // acceptable form. Any skew delay that cannot be folded against the module's
  // parameter scope (e.g. a reference to a net or variable) violates the rule.
  ScopeMap skew_scope = mod ? BuildParamScope(mod) : ScopeMap{};
  CheckClockingSkew(item->default_input_skew_delay, skew_scope,
                    "default input skew", diag_);
  CheckClockingSkew(item->default_output_skew_delay, skew_scope,
                    "default output skew", diag_);
  for (const auto& sig : item->clocking_signals) {
    // §14.3 lets a signal carry its own skew in place of the block's default,
    // so the report names the signal to tell the two apart.
    CheckClockingSkew(sig.skew_delay, skew_scope,
                      ClockingSignalSkewRole(sig, false), diag_);
    CheckClockingSkew(sig.out_skew_delay, skew_scope,
                      ClockingSignalSkewRole(sig, true), diag_);
    CheckClockingOutputBinding(sig, diag_);
  }

  if (!item->name.empty()) {
    auto& sigs = clocking_signals_[item->name];
    for (const auto& sig : item->clocking_signals) {
      sigs[sig.name] = {sig.direction};
    }
  }
}

void Elaborator::ValidateNoFormalShadowedByBodyLocal(ModuleItem* item) {
  // §16.10: a formal-argument identifier cannot be redeclared in the body of
  // the same sequence/property declaration as an
  // assertion_variable_declaration. The two name lists are harvested by the
  // parser; the elaborator only has to flag any overlap.
  if (item->prop_formals.empty() || item->prop_seq_assert_vars.empty()) {
    return;
  }
  std::unordered_set<std::string_view> formal_set(item->prop_formals.begin(),
                                                  item->prop_formals.end());
  for (auto body_var : item->prop_seq_assert_vars) {
    if (formal_set.count(body_var) != 0) {
      diag_.Error(item->loc,
                  "local variable \"" + std::string(body_var) +
                      "\" is a formal argument and cannot be redeclared "
                      "in the body",
                  Subclause("16.10"));
    }
  }
}

void Elaborator::ValidateRecursiveProperty(const ModuleItem* item) {
  if (item == nullptr || item->kind != ModuleItemKind::kPropertyDecl) return;

  const bool kRecursive = property_registry_.IsRecursiveProperty(item);

  // §16.12.17 Restriction 2 / §F.7 RESTRICTION 2: disable iff cannot be used in
  // the declaration of a recursive property. (This mirrors the rule that
  // disable iff cannot be nested.) The accept_on/reject_on family is *not*
  // affected: those operators may appear inside a recursive property.
  if (kRecursive && item->prop_disable_iff_count > 0) {
    diag_.Error(item->loc,
                "recursive property \"" + std::string(item->name) +
                    "\" may not use disable iff (Restriction 2)",
                Subclause("16.12.17"));
  }

  // §16.12.17 Restriction 1 / §F.7 RESTRICTION 1: the negation operator not and
  // the strong operators (s_nexttime, s_eventually, s_always, s_until,
  // s_until_with) cannot be applied to a property expression that instantiates
  // a property from which a recursive property is reachable.
  for (auto ref : item->prop_negated_instance_refs) {
    const ModuleItem* callee = property_registry_.Find(ref);
    if (callee != nullptr &&
        property_registry_.ReachesRecursiveProperty(callee)) {
      diag_.Error(item->loc,
                  "negation or strong operator applied to property \"" +
                      std::string(ref) +
                      "\", which reaches a recursive property "
                      "(Restriction 1)",
                  Subclause("16.12.17"));
    }
  }

  // §16.12.17 Restriction 3 / §F.7 RESTRICTION 3: every recursive instance must
  // occur after a positive advance in time. Equivalently, every cycle of the
  // dependency digraph must have a positive weight sum, so a cycle whose edges
  // are all untimed (weight zero) is illegal. This rejects a self-instantiation
  // with no intervening time advance and the mutually recursive case in which a
  // group of properties instantiate one another with no time advance anywhere
  // on the cycle.
  if (property_registry_.IsOnZeroWeightCycle(item)) {
    diag_.Error(item->loc,
                "recursive property \"" + std::string(item->name) +
                    "\" lies on a recursion cycle with no positive advance in "
                    "time (Restriction 3)",
                Subclause("16.12.17"));
  }

  // §16.12.17 Restriction 4 / §F.7 RESTRICTION 4 applies to every recursive
  // instance regardless of whether the enclosing property is itself recursive.
  ValidateRecursivePropertyArguments(item);
}

namespace {

// §16.12.17 Restriction 4: whether actual argument `i` of recursive instance
// `inst` (of property `q`) violates the rule. Legal when (a) it is itself a
// single formal of p, (b) no formal of p appears, or (c) bound to a local of q.
bool RecursiveInstanceArgViolates(
    const PropertyInstanceArgInfo& inst, const ModuleItem* q, std::size_t i,
    const std::unordered_set<std::string_view>& p_formals) {
  const auto& idents = inst.arg_idents[i];

  // (a) the actual argument expression e is itself a formal of p.
  const bool kIsSingleFormal =
      i < inst.arg_is_single_ident.size() && inst.arg_is_single_ident[i] &&
      idents.size() == 1 && p_formals.count(idents[0]) != 0;
  if (kIsSingleFormal) return false;

  // (b) no formal argument of p appears in e.
  bool any_p_formal = false;
  for (auto id : idents) {
    if (p_formals.count(id) != 0) {
      any_p_formal = true;
      break;
    }
  }
  if (!any_p_formal) return false;

  // (c) e is bound to a local variable formal argument of q (positional).
  const bool kBoundToLocalFormal =
      i < q->prop_formal_is_local.size() && q->prop_formal_is_local[i];
  return !kBoundToLocalFormal;
}

}  // namespace

void Elaborator::ValidateRecursivePropertyArguments(const ModuleItem* item) {
  if (item->prop_instance_args.empty()) return;

  // Formal arguments of the enclosing property p.
  std::unordered_set<std::string_view> p_formals(item->prop_formals.begin(),
                                                 item->prop_formals.end());

  for (const auto& inst : item->prop_instance_args) {
    const ModuleItem* q = property_registry_.Find(inst.callee);
    if (q == nullptr || q->kind != ModuleItemKind::kPropertyDecl) continue;
    // Restriction 4 constrains only instances of a property that participates
    // in the recursion (a recursive instance).
    if (!property_registry_.ReachesRecursiveProperty(q)) continue;

    for (std::size_t i = 0; i < inst.arg_idents.size(); ++i) {
      if (!RecursiveInstanceArgViolates(inst, q, i, p_formals)) continue;
      diag_.Error(item->loc,
                  "recursive instance of \"" + std::string(inst.callee) +
                      "\" passes an actual argument that contains a formal of "
                      "\"" +
                      std::string(item->name) +
                      "\" yet is neither a formal itself nor bound to a local "
                      "variable formal (Restriction 4)",
                  Subclause("16.12.17"));
    }
  }
}

namespace {

// Report a clockvar direction violation for a member-access expression `e`: a
// write (lvalue) to an input clockvar or a read from an output clockvar.
// (Templated so the private nested info type need not be named here.)
template <typename ClockingSignalMap>
void CheckClockvarMemberAccessDirection(
    const Expr* e, bool is_lvalue, const ClockingSignalMap& clocking_signals,
    DiagEngine& diag) {
  if (e->kind != ExprKind::kMemberAccess || !e->lhs ||
      e->lhs->kind != ExprKind::kIdentifier) {
    return;
  }
  auto block_it = clocking_signals.find(e->lhs->text);
  if (block_it == clocking_signals.end()) return;
  std::string_view member;
  if (e->rhs && e->rhs->kind == ExprKind::kIdentifier) {
    member = e->rhs->text;
  } else if (!e->text.empty()) {
    member = e->text;
  }
  if (member.empty()) return;
  auto sig_it = block_it->second.find(member);
  if (sig_it == block_it->second.end()) return;
  if (is_lvalue && sig_it->second.direction == Direction::kInput) {
    diag.Error(
        e->range.start,
        std::format("write to input clockvar '{}.{}'", e->lhs->text, member),
        Subclause("14.3"));
  }
  if (!is_lvalue && sig_it->second.direction == Direction::kOutput) {
    diag.Error(
        e->range.start,
        std::format("read from output clockvar '{}.{}'", e->lhs->text, member),
        Subclause("14.3"));
  }
}

}  // namespace

void Elaborator::CheckClockvarAccessExpr(const Expr* e, bool is_lvalue) {
  if (!e) return;
  CheckClockvarMemberAccessDirection(e, is_lvalue, clocking_signals_, diag_);

  if (!is_lvalue) {
    CheckClockvarAccessExpr(e->lhs, false);
    CheckClockvarAccessExpr(e->rhs, false);
    CheckClockvarAccessExpr(e->condition, false);
    CheckClockvarAccessExpr(e->true_expr, false);
    CheckClockvarAccessExpr(e->false_expr, false);
    for (auto* arg : e->args) CheckClockvarAccessExpr(arg, false);
    for (auto* elem : e->elements) CheckClockvarAccessExpr(elem, false);
  }
}

void Elaborator::WalkStmtsForClockvarAccess(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckClockvarAccessExpr(s->lhs, true);
    CheckClockvarAccessExpr(s->rhs, false);
  } else {
    CheckClockvarAccessExpr(s->expr, false);
    CheckClockvarAccessExpr(s->rhs, false);
  }
  // §14.3 states the input and output clockvar rules of a clocking block and
  // names no statement a clockvar access is exempt in, so this descends every
  // link ForEachChildStmt in elaborator_validate_internal.h names. It wrote out
  // six of the thirteen, and an access in any of the other seven -- a fork arm,
  // a for initialization or step, a randcase item, either arm of an assertion
  // action block, or a randsequence production -- was never looked at.
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForClockvarAccess(sub); });
}

void Elaborator::ValidateClockvarAccess(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForClockvarAccess(item->body);
    }
  }
}

static bool HasCycleDelay(const Stmt* s) {
  if (!s) return false;
  if (s->kind == StmtKind::kCycleDelay) return true;
  // §14.11 says "If no default clocking has been specified for the current
  // module, interface, checker, or program, then the compiler shall issue an
  // error." It conditions that on the module and not on the statement the delay
  // is written in, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h names. It wrote out six of the thirteen,
  // which is what let `initial begin fork ##1; join end` elaborate clean in a
  // module with no default clocking while the same `##1;` written one level up
  // was reported: the walk never read Stmt::fork_stmts, so
  // Elaborator::ValidateCycleDelayDefaultClocking concluded the module wrote no
  // cycle delay.
  //
  // ForEachChildStmt gives the visitor no way to stop, so the first hit is kept
  // in `found` and the recursion runs only while `found` is false.
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = HasCycleDelay(sub);
  });
  return found;
}

// One statement tree written in a module, together with the item that holds it.
// The location is the item's, which is where a report about the whole tree
// stands.
struct ProceduralRoot {
  const ModuleItem* item = nullptr;
  const Stmt* body = nullptr;
};

// Every statement tree of `items`, including those a generate construct or a
// subroutine holds rather than a process.
//
// §14.11 (printed page 361) states that "if no default clocking has been
// specified for the current module, interface, checker, or program, then the
// compiler shall issue an error", and §14.12 (printed page 361) makes one
// clocking block the default "for all cycle delay operations within a given
// module, interface, program, or checker". Neither rule is stated against a
// process, and neither is the sentence that "cycle delay timing controls shall
// not be legal for use in intra-assignment delays". So a ## written in a
// generate block or in a task or function body of a module is judged by the
// same default clocking as one written in an always block beside it, and a walk
// that reads ModuleItem::body off the items of the module reaches only the
// last of those.
//
// A generate construct holds its items in gen_body, in gen_else->gen_body and
// in the body of each entry of gen_case_items, which is the shape
// ValidateConstFuncCallsInGenerate walks in
// src/elaborator/elaborator_validate_funcchecks.cpp. A task or a function
// holds a vector of statements in func_body_stmts rather than the single body a
// process holds, so each of those is a root of its own.
static void CollectProceduralRoots(const std::vector<ModuleItem*>& items,
                                   std::vector<ProceduralRoot>& out);

// The statements of a task or function body, each a root of its own.
static void CollectSubroutineRoots(const ModuleItem* item,
                                   std::vector<ProceduralRoot>& out) {
  for (const auto* stmt : item->func_body_stmts) {
    if (stmt) out.push_back({item, stmt});
  }
}

// The roots of every item a generate construct holds, in its then body, its
// else body and each of its case arms.
static void CollectGenerateRoots(const ModuleItem* item,
                                 std::vector<ProceduralRoot>& out) {
  CollectProceduralRoots(item->gen_body, out);
  if (item->gen_else) CollectProceduralRoots(item->gen_else->gen_body, out);
  for (const auto& ci : item->gen_case_items) {
    CollectProceduralRoots(ci.body, out);
  }
}

static void CollectProceduralRoots(const std::vector<ModuleItem*>& items,
                                   std::vector<ProceduralRoot>& out) {
  for (const auto* item : items) {
    switch (item->kind) {
      case ModuleItemKind::kAlwaysBlock:
      case ModuleItemKind::kAlwaysCombBlock:
      case ModuleItemKind::kAlwaysFFBlock:
      case ModuleItemKind::kAlwaysLatchBlock:
      case ModuleItemKind::kInitialBlock:
      case ModuleItemKind::kFinalBlock:
        if (item->body) out.push_back({item, item->body});
        break;
      case ModuleItemKind::kFunctionDecl:
      case ModuleItemKind::kTaskDecl:
        CollectSubroutineRoots(item, out);
        break;
      case ModuleItemKind::kGenerateIf:
      case ModuleItemKind::kGenerateCase:
      case ModuleItemKind::kGenerateFor:
        CollectGenerateRoots(item, out);
        break;
      default:
        break;
    }
  }
}

void Elaborator::ValidateCycleDelayDefaultClocking(const ModuleDecl* decl) {
  bool has_default = false;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking) {
      has_default = true;
      break;
    }
  }
  if (has_default) return;
  std::vector<ProceduralRoot> roots;
  CollectProceduralRoots(decl->items, roots);
  // A subroutine contributes one root per statement of its body, so a second ##
  // in the same task would otherwise earn a second report at the same location.
  const ModuleItem* reported = nullptr;
  for (const auto& root : roots) {
    if (root.item == reported || !HasCycleDelay(root.body)) continue;
    reported = root.item;
    diag_.Error(root.item->loc,
                "cycle delay (##) requires a default clocking block",
                Subclause("14.11"));
  }
}

// §14.11: locate an assignment that carries a cycle-delay intra-assignment
// timing control. A leading cycle delay is legal only on a synchronous drive
// (§14.16), which targets a writable clocking-block variable reached through a
// member access such as cb.sig, optionally wrapped in a bit-select or slice
// (cb.sig[2]). Every other assignment target -- a simple name, a bit-/part-
// select of an ordinary variable, a concatenation, or a member of a
// non-clocking object -- makes the ## an illegal intra-assignment delay.
// Discriminating on the clockvar predicate rather than on the bare-name shape
// catches those select and concatenation forms too. The walk returns the
// offending statement so its source location can be reported.
static const Stmt* FindIntraAssignCycleDelay(
    const Stmt* s, const ClockvarPredicate& targets_writable) {
  if (!s) return nullptr;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->cycle_delay != nullptr && s->lhs != nullptr &&
      !targets_writable(s->lhs)) {
    return s;
  }
  // §14.11 admits a leading cycle delay on a synchronous drive alone and names
  // no statement the rule is suspended in, so this descends every link
  // ForEachChildStmt in elaborator_validate_internal.h names. It wrote out six
  // of the thirteen, so an illegal intra-assignment `##` in a fork arm, a
  // randcase item, an assertion action block or a randsequence production went
  // unreported.
  //
  // ForEachChildStmt gives the visitor no way to stop, so the first offending
  // statement is kept in `hit` and the recursion runs only while `hit` is null.
  // That is what makes this walk report the first one in source order rather
  // than whichever link the list happens to visit last.
  const Stmt* hit = nullptr;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (hit) return;
    hit = FindIntraAssignCycleDelay(sub, targets_writable);
  });
  return hit;
}

void Elaborator::ValidateIntraAssignCycleDelay(const ModuleDecl* decl) {
  const ClockvarPredicate kTargetsWritable = [this](const Expr* e) {
    return ExprTargetsWritableClockvar(e);
  };
  std::vector<ProceduralRoot> roots;
  CollectProceduralRoots(decl->items, roots);
  // One report per item, as for the missing default clocking above: a
  // subroutine contributes one root per statement of its body.
  const ModuleItem* reported = nullptr;
  for (const auto& root : roots) {
    if (root.item == reported) continue;
    const Stmt* hit = FindIntraAssignCycleDelay(root.body, kTargetsWritable);
    if (hit == nullptr) continue;
    reported = root.item;
    diag_.Error(hit->range.start,
                "cycle delay (##) is not a legal intra-assignment delay "
                "in a blocking or nonblocking assignment",
                Subclause("14.11"));
  }
}

void Elaborator::ValidateDuplicateDefaultClocking(const ModuleDecl* decl) {
  const ModuleItem* first_default = nullptr;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking) {
      if (first_default) {
        diag_.Error(item->loc,
                    "only one default clocking block is allowed per scope",
                    Subclause("14.12"));
        return;
      }
      first_default = item;
    }
  }
}

namespace {

// §14.12: true when some inline clocking block (carrying an @(event)) other
// than `target` shares its name, so `target` names a real clocking block.
bool DefaultClockingNamesBlock(const ModuleDecl* decl,
                               const ModuleItem* target) {
  for (const auto* other : decl->items) {
    if (other == target) continue;
    if (other->kind == ModuleItemKind::kClockingBlock &&
        !other->clocking_event.empty() && other->name == target->name) {
      return true;
    }
  }
  return false;
}

}  // namespace

void Elaborator::ValidateDefaultClockingReference(const ModuleDecl* decl) {
  // §14.12: a "default clocking <id>;" assignment statement designates an
  // existing clocking block as the default. Its clocking_identifier shall be
  // the name of a clocking block. The assignment form is distinguished from
  // the inline declaration form by carrying no clocking event (the inline
  // form always declares an @(event)).
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kClockingBlock) continue;
    if (!item->is_default_clocking) continue;
    if (!item->clocking_event.empty()) continue;  // inline declaration form
    if (item->name.empty()) continue;
    if (!DefaultClockingNamesBlock(decl, item)) {
      diag_.Error(item->loc,
                  "default clocking \"" + std::string(item->name) +
                      "\" does not name a clocking block",
                  Subclause("14.12"));
    }
  }
}

void Elaborator::ValidateContAssignToClockvar(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    if (!item->assign_lhs) continue;
    // §14.16.2: a continuous assignment to a variable that is associated with
    // an output (or inout) clockvar is illegal. The target may be the whole
    // variable or a bit-/part-select of it, so resolve through any selects to
    // the root identifier; a select target is rejected exactly as the whole
    // variable would be. This mirrors the root resolution the primitive and
    // procedural-continuous checks already perform for the same prohibition.
    const Expr* root = item->assign_lhs;
    while (root != nullptr && root->kind == ExprKind::kSelect)
      root = root->base;
    if (root == nullptr || root->kind != ExprKind::kIdentifier) continue;
    if (IsOutputClockvarSignal(root->text)) {
      diag_.Error(item->loc,
                  std::format("continuous assignment to clocking output "
                              "variable '{}'",
                              root->text),
                  Subclause("14.16.2"));
    }
  }
}

bool Elaborator::IsOutputClockvarSignal(std::string_view name) const {
  // §14.16.2: a clocking output/inout is implicitly tied to a same-named signal
  // in the enclosing scope (§14.3). Match the bare variable name against the
  // output/inout clockvar members collected across every clocking block.
  for (const auto& [block_name, sigs] : clocking_signals_) {
    auto it = sigs.find(name);
    if (it != sigs.end() && (it->second.direction == Direction::kOutput ||
                             it->second.direction == Direction::kInout)) {
      return true;
    }
  }
  return false;
}

namespace {

// §14.16.2: it shall be illegal to drive a variable associated with an output
// clockvar from a primitive (the gate-output terminal `t` resolved to its
// root).
void CheckPrimitiveOutputTerminal(
    const Expr* t, const OutputClockvarNamePredicate& is_output_clockvar,
    DiagEngine& diag) {
  const Expr* root = t;
  while (root != nullptr && root->kind == ExprKind::kSelect) root = root->base;
  if (root != nullptr && root->kind == ExprKind::kIdentifier &&
      is_output_clockvar(root->text)) {
    diag.Error(root->range.start,
               std::format("primitive output drives variable '{}', which is "
                           "associated with a clocking output",
                           root->text),
               Subclause("14.16.2"));
  }
}

// Check the output terminal(s) of one gate instance. For buf/not gates every
// terminal but the last is an output; otherwise the first terminal is the one
// output.
void CheckGateInstOutputTerminals(
    const ModuleItem* item,
    const OutputClockvarNamePredicate& is_output_clockvar, DiagEngine& diag) {
  const auto& terms = item->gate_terminals;
  if (terms.empty()) return;
  if (item->gate_kind == GateKind::kBuf || item->gate_kind == GateKind::kNot) {
    for (size_t i = 0; i + 1 < terms.size(); ++i) {
      CheckPrimitiveOutputTerminal(terms[i], is_output_clockvar, diag);
    }
  } else {
    CheckPrimitiveOutputTerminal(terms[0], is_output_clockvar, diag);
  }
}

}  // namespace

void Elaborator::ValidatePrimitiveDriveToClockvar(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  const OutputClockvarNamePredicate kIsOutputClockvar =
      [this](std::string_view name) { return IsOutputClockvarSignal(name); };
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kGateInst) continue;
    CheckGateInstOutputTerminals(item, kIsOutputClockvar, diag_);
  }
}

// §14.16: a synchronous drive reaches a clocking-block output (or inout)
// through a member access such as cb.sig, optionally wrapped in a bit-select
// or slice (cb.sig[2], cb.sig[8:2]). Returns true when `e` designates such a
// writable clockvar. Input clockvars are excluded here; writes to them are
// rejected separately by the clockvar-access check.
bool Elaborator::ExprTargetsWritableClockvar(const Expr* e) const {
  while (e != nullptr && e->kind == ExprKind::kSelect) e = e->base;
  if (e == nullptr || e->kind != ExprKind::kMemberAccess || e->lhs == nullptr ||
      e->lhs->kind != ExprKind::kIdentifier)
    return false;
  auto block_it = clocking_signals_.find(e->lhs->text);
  if (block_it == clocking_signals_.end()) return false;
  std::string_view member;
  if (e->rhs && e->rhs->kind == ExprKind::kIdentifier)
    member = e->rhs->text;
  else if (!e->text.empty())
    member = e->text;
  if (member.empty()) return false;
  auto sig_it = block_it->second.find(member);
  if (sig_it == block_it->second.end()) return false;
  return sig_it->second.direction == Direction::kOutput ||
         sig_it->second.direction == Direction::kInout;
}

namespace {

// Validate the synchronous-drive form of a blocking/nonblocking assignment.
void CheckSyncDriveAssign(const Stmt* s,
                          const ClockvarPredicate& targets_writable,
                          DiagEngine& diag) {
  if (targets_writable(s->lhs)) {
    // §14.16: the only timing control permitted on a synchronous drive is a
    // leading cycle delay (## ...). A regular intra-assignment delay (# ...)
    // is not a legal form of synchronous drive to a clockvar.
    if (s->delay != nullptr) {
      diag.Error(s->delay->range.start,
                 "intra-assignment delay (#) is not a legal synchronous "
                 "drive to a clocking output variable",
                 Subclause("14.16"));
    }
  }
  // §14.16: the clockvar_expression of a synchronous drive is a bit-select,
  // slice, or whole clockvar; a concatenation target is not allowed.
  if (s->lhs != nullptr && s->lhs->kind == ExprKind::kConcatenation) {
    for (const auto* elem : s->lhs->elements) {
      if (targets_writable(elem)) {
        diag.Error(s->lhs->range.start,
                   "a concatenation is not a legal synchronous drive target "
                   "for a clocking output variable",
                   Subclause("14.16"));
        break;
      }
    }
  }
}

// Validate a procedural continuous assignment (assign/force) arm.
void CheckSyncDriveProcContAssign(
    const Stmt* s, const ClockvarPredicate& targets_writable,
    const OutputClockvarNamePredicate& is_output_clockvar, DiagEngine& diag) {
  // §14.16: writing to a clockvar by any means other than a synchronous
  // drive is an error; procedural continuous assignment (assign/force) is
  // explicitly disallowed.
  if (targets_writable(s->lhs)) {
    diag.Error(s->lhs->range.start,
               "procedural continuous assignment (assign/force) to a "
               "clocking output variable is not allowed",
               Subclause("14.16"));
  } else if (s->lhs != nullptr) {
    // §14.16.2: it is likewise illegal to write the underlying variable that
    // an output clockvar is tied to with a procedural continuous assignment.
    const Expr* root = s->lhs;
    while (root != nullptr && root->kind == ExprKind::kSelect)
      root = root->base;
    if (root != nullptr && root->kind == ExprKind::kIdentifier &&
        is_output_clockvar(root->text)) {
      diag.Error(
          root->range.start,
          std::format("procedural continuous assignment (assign/force) to "
                      "variable '{}', which is associated with a clocking "
                      "output, is not allowed",
                      root->text),
          Subclause("14.16.2"));
    }
  }
}

}  // namespace

void Elaborator::WalkStmtsForSyncDriveForm(const Stmt* s) {
  if (!s) return;
  const ClockvarPredicate kTargetsWritable = [this](const Expr* e) {
    return ExprTargetsWritableClockvar(e);
  };
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckSyncDriveAssign(s, kTargetsWritable, diag_);
  } else if (s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign) {
    const OutputClockvarNamePredicate kIsOutputClockvar =
        [this](std::string_view name) { return IsOutputClockvarSignal(name); };
    CheckSyncDriveProcContAssign(s, kTargetsWritable, kIsOutputClockvar, diag_);
  }
  // §14.16 and §14.16.2 state the form a synchronous drive takes and name no
  // statement the form is not required in, so this descends every link
  // ForEachChildStmt in elaborator_validate_internal.h names. It wrote out six
  // of the thirteen, so a malformed drive in a fork arm, a randcase item, an
  // assertion action block or a randsequence production reached neither
  // CheckSyncDriveAssign nor CheckSyncDriveProcContAssign.
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForSyncDriveForm(sub); });
}

void Elaborator::ValidateSyncDriveForm(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) WalkStmtsForSyncDriveForm(item->body);
  }
}

}  // namespace delta
