#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/always_range.h"
#include "elaborator/assertion_rules.h"
#include "elaborator/assertion_walk.h"
#include "elaborator/const_eval.h"
#include "elaborator/dollar_contexts.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/nexttime_index.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

using NameSet = std::unordered_set<std::string_view>;

struct BoundEnv {
  const NamedDecls& decls;
  DiagEngine& diag;
  std::unordered_set<const ModuleItem*> active;
};

struct BoundScope {
  const ScopeMap& values;
  const NameSet& unbounded;
  const NameSet& formals;
  bool formals_only = false;
};

bool IsLiteralBound(const Expr* e) {
  const Expr* magnitude =
      e->kind == ExprKind::kUnary && e->op == TokenKind::kMinus ? e->lhs : e;
  return magnitude->kind == ExprKind::kIntegerLiteral;
}

bool Checks(const Expr* e, const BoundScope& scope) {
  return e != nullptr && !IsLiteralBound(e) &&
         ExprMentionsAny(e, scope.formals) == scope.formals_only;
}

std::optional<int64_t> Fold(const Expr* e, uint32_t value,
                            const BoundScope& scope) {
  if (e != nullptr || value == SeqCycleDelay::kUnbounded) {
    return ConstEvalInt(e, scope.values);
  }
  return value;
}

void CheckDelay(const SeqCycleDelay& delay, const BoundScope& scope,
                DiagEngine& diag) {
  if (!Checks(delay.min_expr, scope) && !Checks(delay.max_expr, scope)) {
    return;
  }
  const Expr* at = delay.min_expr != nullptr ? delay.min_expr : delay.max_expr;
  int64_t lo = Fold(delay.min_expr, delay.min, scope).value_or(0);
  int64_t hi = Fold(delay.max_expr, delay.max, scope).value_or(INT64_MAX);
  if (std::min(lo, hi) < 0) {
    diag.Error(at->range.start, "a cycle delay shall be 0 or greater",
               Subclause("16.7"));
  } else if (hi < lo) {
    diag.Error(at->range.start,
               "the maximum of a cycle delay range shall be no less than "
               "its minimum",
               Subclause("16.7"));
  }
}

void CheckBodyDelays(const SeqLinearBody& body, const BoundScope& scope,
                     DiagEngine& diag) {
  ForEachBody(body, [&](const SeqLinearBody& b) {
    for (const SeqCycleDelay& delay : b.delays) CheckDelay(delay, scope, diag);
  });
}

void CheckNexttime(const PropertyExprNode& node, const BoundScope& scope,
                   DiagEngine& diag) {
  if (!Checks(node.boolean, scope)) return;
  std::optional<int64_t> index = ConstEvalInt(node.boolean, scope.values);
  NexttimeIndex folded;
  folded.is_constant = index.has_value();
  folded.is_integer = index.has_value();
  folded.value = index.value_or(0);
  if (IsNexttimeIndexWellFormed(folded)) return;
  diag.Error(node.boolean->range.start,
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

void CheckRange(const PropertyExprNode& node, const BoundScope& scope,
                DiagEngine& diag) {
  if (!Checks(node.range_min, scope) && !Checks(node.range_max, scope)) {
    return;
  }
  AlwaysRange range;
  range.min = FoldedBound(node.range_min, scope);
  range.max = node.range_unbounded ? MakeAlwaysDollar()
                                   : FoldedBound(node.range_max, scope);
  if (IsAlwaysRangeWellFormed(range, false)) return;
  bool always = node.kind == PropertyExprNode::Kind::kAlways;
  diag.Error(node.range_min->range.start,
             std::string(always ? "always" : "eventually") +
                 " range bounds shall be non-negative integer constant "
                 "expressions, the minimum no greater than the maximum",
             Subclause(always ? "16.12.11" : "16.12.13"));
}

const Expr* ActualOf(const Expr* call, const ModuleItem* decl, size_t i) {
  const Expr* actual = i < call->args.size() ? call->args[i] : nullptr;
  return actual != nullptr ? actual : decl->prop_formal_defaults[i];
}

void CheckDollarActuals(const Expr* call, const ModuleItem* decl,
                        DiagEngine& diag) {
  const char* clause =
      decl->kind == ModuleItemKind::kSequenceDecl ? "16.8" : "16.12";
  for (size_t i = 0; i < decl->prop_formals.size(); ++i) {
    if (!IsNameRef(ActualOf(call, decl, i), "$") || FormalAdmitsDollar(decl, i))
      continue;
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

void CheckInstance(const Expr* call, const ModuleItem* seq,
                   const BoundScope& outer, BoundEnv& env) {
  CheckDollarActuals(call, seq, env.diag);
  ScopeMap values = outer.values;
  const NameSet kFormals(seq->prop_formals.begin(), seq->prop_formals.end());
  for (size_t i = 0; i < seq->prop_formals.size(); ++i) {
    std::optional<int64_t> value =
        ConstEvalInt(ActualOf(call, seq, i), outer.values);
    if (value.has_value()) values[seq->prop_formals[i]] = *value;
  }
  if (!env.active.insert(seq).second) return;
  const BoundScope kInner{values, outer.unbounded, kFormals, true};
  CheckBodyDelays(seq->seq_linear, kInner, env.diag);
  ForEachBodyExpr(seq->seq_linear,
                  [&](const Expr* e) { CheckOperand(e, kInner, env); });
  env.active.erase(seq);
}

void CheckOperand(const Expr* e, const BoundScope& scope, BoundEnv& env) {
  ForEachSubExpr(e, [&](const Expr* sub) {
    const ModuleItem* decl = InstantiatedDecl(sub, env.decls);
    if (decl != nullptr) CheckInstance(sub, decl, scope, env);
  });
}

void CheckSequenceItem(const ModuleItem* seq, const BoundScope& scope,
                       BoundEnv& env) {
  CheckBodyDelays(seq->seq_linear, scope, env.diag);
  ForEachBodyExpr(seq->seq_linear,
                  [&](const Expr* e) { CheckOperand(e, scope, env); });
}

bool HoldsDollar(const Expr* e, const BoundScope& scope) {
  return ContainsDollar(e) || ExprMentionsAny(e, scope.unbounded);
}

void CheckTree(const PropertyExprNode* node, const BoundScope& scope,
               BoundEnv& env) {
  ForEachTreeNode(node, [&](const PropertyExprNode& n) {
    using Kind = PropertyExprNode::Kind;
    if (n.kind == Kind::kNexttime) {
      CheckNexttime(n, scope, env.diag);
    } else if (n.kind == Kind::kAlways || n.kind == Kind::kEventually) {
      if (!HoldsDollar(n.range_min, scope) && !HoldsDollar(n.range_max, scope))
        CheckRange(n, scope, env.diag);
    } else {
      CheckOperand(n.boolean, scope, env);
    }
    if (n.sequence != nullptr) CheckSequenceItem(n.sequence, scope, env);
  });
}

}  // namespace

bool FormalAdmitsDollar(const ModuleItem* decl, size_t i) {
  std::string_view name = decl->prop_formals[i];
  FormalReferences refs;
  CountFormalInBody(decl->seq_linear, name, refs);
  CountFormalInExpr(decl->prop_body_expr, name, refs);
  CountFormalInTree(decl->prop_body_tree, name, refs);
  return decl->prop_formal_type_kw[i] == TokenKind::kKwUntyped &&
         refs.all == refs.permitted;
}

void ValidateAssertionBoundRules(const ModuleDecl* decl, const ScopeMap& params,
                                 const NameSet& unbounded, DiagEngine& diag) {
  const NamedDecls kNamed = NamedDeclsByName(decl, true);
  BoundEnv env{kNamed, diag, {}};
  for (const ModuleItem* item : decl->items) {
    if (kNamed.count(item->name) == 0) continue;
    const NameSet kFormals(item->prop_formals.begin(),
                           item->prop_formals.end());
    NameSet own_unbounded = unbounded;
    for (std::string_view formal : item->prop_formals)
      own_unbounded.erase(formal);
    const BoundScope kOwn{params, own_unbounded, kFormals, false};
    CheckSequenceItem(item, kOwn, env);
    CheckTree(item->prop_body_tree, kOwn, env);
  }
  const NameSet kNone;
  const BoundScope kModule{params, unbounded, kNone, false};
  ForEachConcurrentAssertion(decl, [&](const Stmt* s) {
    CheckTree(s->assert_property, kModule, env);
    if (s->assert_sequence != nullptr) {
      CheckSequenceItem(s->assert_sequence, kModule, env);
    }
  });
}

}  // namespace delta
