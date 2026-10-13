#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/always_range.h"
#include "elaborator/assertion_rules.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/nexttime_index.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

using NameSet = std::unordered_set<std::string_view>;
using SequenceMap = std::unordered_map<std::string_view, const ModuleItem*>;

// The module's named sequences and properties by name, the diagnostics sink,
// and the declarations whose instance is being followed, so a cyclic
// instantiation, which §16.8 makes illegal on its own account, ends the walk.
struct BoundEnv {
  const SequenceMap& sequences;
  DiagEngine& diag;
  std::unordered_set<const ModuleItem*> active;
};

// The bounds one pass folds and checks. A declaration's own pass, with
// `formals_only` false, checks the bounds that name none of its `formals`,
// with the module's parameters in `values`; the pass an instance makes over
// the declaration it instantiates, with `formals_only` true, checks the
// bounds that name a formal, with the formals bound to the instance's
// folded actuals in `values` beside the parameters. Every bound is so
// checked once, in the place its value is settled. A bound written as an
// integer literal is the parser's to check.
struct BoundScope {
  const ScopeMap& values;
  const NameSet& formals;
  bool formals_only = false;
};

bool IsLiteralBound(const Expr* e) {
  if (e != nullptr && e->kind == ExprKind::kUnary &&
      e->op == TokenKind::kMinus) {
    e = e->lhs;
  }
  return e != nullptr && e->kind == ExprKind::kIntegerLiteral;
}

bool Checks(const Expr* e, const BoundScope& scope) {
  return e != nullptr && !IsLiteralBound(e) &&
         ExprMentionsAny(e, scope.formals) == scope.formals_only;
}

std::optional<int64_t> Fold(const Expr* e, uint32_t value,
                            const BoundScope& scope) {
  if (e != nullptr) return ConstEvalInt(e, scope.values);
  if (value == SeqCycleDelay::kUnbounded) return std::nullopt;
  return value;
}

// §16.7: a cycle delay, and each bound of a cycle delay range, is 0 or
// greater, and a range's maximum is no less than its minimum.
void CheckDelay(const SeqCycleDelay& delay, const BoundScope& scope,
                DiagEngine& diag) {
  if (!Checks(delay.min_expr, scope) && !Checks(delay.max_expr, scope)) {
    return;
  }
  const Expr* at = delay.min_expr != nullptr ? delay.min_expr : delay.max_expr;
  std::optional<int64_t> lo = Fold(delay.min_expr, delay.min, scope);
  std::optional<int64_t> hi = Fold(delay.max_expr, delay.max, scope);
  if ((lo.has_value() && *lo < 0) || (hi.has_value() && *hi < 0)) {
    diag.Error(at->range.start, "a cycle delay shall be 0 or greater",
               Subclause("16.7"));
  } else if (lo.has_value() && hi.has_value() && *hi < *lo) {
    diag.Error(at->range.start,
               "the maximum of a cycle delay range shall be no less than "
               "its minimum",
               Subclause("16.7"));
  }
}

void CheckBodyDelays(const SeqLinearBody& body, const BoundScope& scope,
                     DiagEngine& diag) {
  for (const SeqCycleDelay& delay : body.delays) {
    CheckDelay(delay, scope, diag);
  }
  for (const SeqLinearBody& inner : body.intersects) {
    CheckBodyDelays(inner, scope, diag);
  }
  for (const SeqLinearBody& inner : body.conjuncts) {
    CheckBodyDelays(inner, scope, diag);
  }
  for (const SeqLinearBody& inner : body.alternatives) {
    CheckBodyDelays(inner, scope, diag);
  }
}

// §16.12.10: the index of nexttime and s_nexttime is a non-negative integer
// constant expression.
void CheckNexttime(const PropertyExprNode* node, const BoundScope& scope,
                   DiagEngine& diag) {
  if (!Checks(node->boolean, scope)) return;
  std::optional<int64_t> index = ConstEvalInt(node->boolean, scope.values);
  NexttimeIndex folded;
  folded.is_constant = index.has_value();
  folded.is_integer = index.has_value();
  folded.value = index.value_or(0);
  if (IsNexttimeIndexWellFormed(folded)) return;
  diag.Error(node->boolean->range.start,
             "the index of nexttime shall be a non-negative integer constant "
             "expression",
             Subclause("16.12.10"));
}

AlwaysRangeBound FoldedBound(const Expr* e, const BoundScope& scope) {
  AlwaysRangeBound bound;
  std::optional<int64_t> value = ConstEvalInt(e, scope.values);
  bound.is_constant = value.has_value();
  bound.is_integer = value.has_value();
  bound.value = value.value_or(0);
  return bound;
}

// §16.12.11 and §16.12.13: the bounds of a ranged always or eventually are
// non-negative integer constant expressions, the minimum no greater than
// the maximum. A `$` maximum is the parser's to judge, so it is read here as
// one a weak operator allows.
void CheckRange(const PropertyExprNode* node, const BoundScope& scope,
                DiagEngine& diag) {
  if (node->range_min == nullptr ||
      (!Checks(node->range_min, scope) && !Checks(node->range_max, scope))) {
    return;
  }
  AlwaysRange range;
  range.min = FoldedBound(node->range_min, scope);
  range.max = node->range_max != nullptr ? FoldedBound(node->range_max, scope)
                                         : MakeAlwaysDollar();
  if (IsAlwaysRangeWellFormed(range, false)) return;
  bool always = node->kind == PropertyExprNode::Kind::kAlways;
  diag.Error(node->range_min->range.start,
             std::string(always ? "always" : "eventually") +
                 " range bounds shall be non-negative integer constant "
                 "expressions, the minimum no greater than the maximum",
             Subclause(always ? "16.12.11" : "16.12.13"));
}

bool IsName(const Expr* e, std::string_view name) {
  return e != nullptr && e->kind == ExprKind::kIdentifier && e->text == name;
}

bool Mentions(const Expr* e, std::string_view name) {
  if (e == nullptr) return false;
  return IsName(e, name) || AnyExprChild(e, [&](const Expr* child) {
           return Mentions(child, name);
         });
}

// Whether `e` reads `name` other than as a whole actual argument of an
// instance.
bool ReadsOtherwise(const Expr* e, std::string_view name) {
  if (e == nullptr) return false;
  if (IsName(e, name)) return true;
  if (e->kind != ExprKind::kCall) {
    return AnyExprChild(
        e, [&](const Expr* child) { return ReadsOtherwise(child, name); });
  }
  for (const Expr* arg : e->args) {
    if (!IsName(arg, name) && ReadsOtherwise(arg, name)) return true;
  }
  return ReadsOtherwise(e->lhs, name);
}

// Whether the bounds of a cycle delay or a repetition read `name` other than
// as the whole upper bound of a range, `##d` and `[*d]` standing for the
// range [d:d] whose lower bound d is.
bool BoundReadsOtherwise(const SeqCycleDelay& bounds, std::string_view name) {
  return Mentions(bounds.min_expr, name) ||
         (!IsName(bounds.max_expr, name) && Mentions(bounds.max_expr, name));
}

bool BoundsReadOtherwise(const SeqLinearBody& body, std::string_view name) {
  for (const SeqCycleDelay& delay : body.delays) {
    if (BoundReadsOtherwise(delay, name)) return true;
  }
  for (const SeqRepetition& rep : body.repetitions) {
    if (BoundReadsOtherwise(rep, name)) return true;
  }
  return false;
}

bool ExprsReadOtherwise(const SeqLinearBody& body, std::string_view name) {
  for (const Expr* operand : body.operands) {
    if (ReadsOtherwise(operand, name)) return true;
  }
  for (const auto& items : body.match_items) {
    for (const SeqMatchAssign& item : items) {
      if (ReadsOtherwise(item.rhs, name) || ReadsOtherwise(item.call, name)) {
        return true;
      }
    }
  }
  for (const SeqThroughout& guard : body.throughouts) {
    if (ReadsOtherwise(guard.cond, name)) return true;
  }
  return false;
}

bool BodyReadsOtherwise(const SeqLinearBody& body, std::string_view name) {
  if (BoundsReadOtherwise(body, name) || ExprsReadOtherwise(body, name)) {
    return true;
  }
  for (const auto* nested :
       {&body.intersects, &body.conjuncts, &body.alternatives}) {
    for (const SeqLinearBody& inner : *nested) {
      if (BodyReadsOtherwise(inner, name)) return true;
    }
  }
  return false;
}

bool TreeReadsOtherwise(const PropertyExprNode* node, std::string_view name) {
  if (node == nullptr) return false;
  if (ReadsOtherwise(node->boolean, name) || Mentions(node->range_min, name) ||
      Mentions(node->range_max, name) ||
      (node->sequence != nullptr &&
       BodyReadsOtherwise(node->sequence->seq_linear, name))) {
    return true;
  }
  for (const PropertyExprNode* operand : node->operands) {
    if (TreeReadsOtherwise(operand, name)) return true;
  }
  return false;
}

// The actual bound to the formal `i` of `decl` by the instance `call`, or by
// the formal's default.
const Expr* ActualOf(const Expr* call, const ModuleItem* decl, size_t i) {
  const Expr* actual = i < call->args.size() ? call->args[i] : nullptr;
  if (actual == nullptr && i < decl->prop_formal_defaults.size()) {
    actual = decl->prop_formal_defaults[i];
  }
  return actual;
}

// Whether the formal `i` of `decl` may be bound to `$`: untyped, and read
// only as a range's upper bound or as an instance's actual.
bool AdmitsDollar(const ModuleItem* decl, size_t i) {
  std::string_view name = decl->prop_formals[i];
  bool untyped = i < decl->prop_formal_type_kw.size() &&
                 decl->prop_formal_type_kw[i] == TokenKind::kKwUntyped;
  return untyped && !BodyReadsOtherwise(decl->seq_linear, name) &&
         !TreeReadsOtherwise(decl->prop_body_tree, name) &&
         !ReadsOtherwise(decl->prop_body_expr, name);
}

// §16.8, and §16.12 for a property: a formal of `decl` bound to `$`, by the
// instance `call` or by its default, is untyped, and each reference to it is
// the upper bound of a cycle delay range or an actual argument of an
// instance.
void CheckDollarActuals(const Expr* call, const ModuleItem* decl,
                        DiagEngine& diag) {
  const char* clause =
      decl->kind == ModuleItemKind::kSequenceDecl ? "16.8" : "16.12";
  for (size_t i = 0; i < decl->prop_formals.size(); ++i) {
    if (!IsName(ActualOf(call, decl, i), "$") || AdmitsDollar(decl, i)) {
      continue;
    }
    diag.Error(call->range.start,
               "$ binds the formal '" + std::string(decl->prop_formals[i]) +
                   "' of '" + std::string(decl->name) +
                   "', which shall be untyped and referenced only as the "
                   "upper bound of a cycle delay range or as an actual "
                   "argument of an instance",
               Subclause(clause));
  }
}

void CheckOperand(const Expr* e, const BoundScope& scope, BoundEnv& env);

void CheckBodyOperands(const SeqLinearBody& body, const BoundScope& scope,
                       BoundEnv& env) {
  for (const Expr* operand : body.operands) {
    CheckOperand(operand, scope, env);
  }
  for (const SeqLinearBody& inner : body.intersects) {
    CheckBodyOperands(inner, scope, env);
  }
  for (const SeqLinearBody& inner : body.conjuncts) {
    CheckBodyOperands(inner, scope, env);
  }
  for (const SeqLinearBody& inner : body.alternatives) {
    CheckBodyOperands(inner, scope, env);
  }
}

// §16.7 and §16.8: an instance of a named sequence settles the bounds its
// declaration writes with a formal; they are checked with each formal bound
// to the instance's actual, folded in the scope the instance stands in.
void CheckInstance(const Expr* call, const ModuleItem* seq,
                   const BoundScope& outer, BoundEnv& env) {
  CheckDollarActuals(call, seq, env.diag);
  ScopeMap values = outer.values;
  NameSet formals;
  for (size_t i = 0; i < seq->prop_formals.size(); ++i) {
    formals.insert(seq->prop_formals[i]);
    const Expr* actual = ActualOf(call, seq, i);
    if (actual == nullptr) continue;
    std::optional<int64_t> value = ConstEvalInt(actual, outer.values);
    if (value.has_value()) values[seq->prop_formals[i]] = *value;
  }
  if (formals.empty() || !env.active.insert(seq).second) return;
  const BoundScope kInner{values, formals, true};
  CheckBodyDelays(seq->seq_linear, kInner, env.diag);
  CheckBodyOperands(seq->seq_linear, kInner, env);
  env.active.erase(seq);
}

void CheckOperand(const Expr* e, const BoundScope& scope, BoundEnv& env) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kCall) {
    auto it = env.sequences.find(e->callee);
    if (it != env.sequences.end()) {
      CheckInstance(e, it->second, scope, env);
    }
  }
  ForEachExprChild(e,
                   [&](const Expr* child) { CheckOperand(child, scope, env); });
}

void CheckSequenceItem(const ModuleItem* seq, const BoundScope& scope,
                       BoundEnv& env) {
  if (seq == nullptr) return;
  CheckBodyDelays(seq->seq_linear, scope, env.diag);
  CheckBodyOperands(seq->seq_linear, scope, env);
}

void CheckTree(const PropertyExprNode* node, const BoundScope& scope,
               BoundEnv& env) {
  if (node == nullptr) return;
  using Kind = PropertyExprNode::Kind;
  if (node->kind == Kind::kNexttime) {
    CheckNexttime(node, scope, env.diag);
  } else if (node->kind == Kind::kAlways || node->kind == Kind::kEventually) {
    CheckRange(node, scope, env.diag);
  } else {
    CheckOperand(node->boolean, scope, env);
  }
  CheckSequenceItem(node->sequence, scope, env);
  for (const PropertyExprNode* operand : node->operands) {
    CheckTree(operand, scope, env);
  }
}

void CheckAssertion(const Stmt* s, const BoundScope& scope, BoundEnv& env) {
  CheckTree(s->assert_property, scope, env);
  CheckSequenceItem(s->assert_sequence, scope, env);
}

}  // namespace

void ValidateAssertionBoundRules(const ModuleDecl* decl, const ScopeMap& params,
                                 DiagEngine& diag) {
  const SequenceMap kNamed = NamedDeclsByName(decl, true);
  BoundEnv env{kNamed, diag, {}};
  for (const ModuleItem* item : decl->items) {
    if (item->kind != ModuleItemKind::kSequenceDecl &&
        item->kind != ModuleItemKind::kPropertyDecl) {
      continue;
    }
    const NameSet kFormals(item->prop_formals.begin(),
                           item->prop_formals.end());
    const BoundScope kOwn{params, kFormals, false};
    CheckSequenceItem(item, kOwn, env);
    CheckTree(item->prop_body_tree, kOwn, env);
  }
  const NameSet kNone;
  const BoundScope kModule{params, kNone, false};
  ForEachConcurrentAssertion(
      decl, [&](const Stmt* s) { CheckAssertion(s, kModule, env); });
}

}  // namespace delta
