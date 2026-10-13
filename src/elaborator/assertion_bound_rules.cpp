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
#include "elaborator/elaborator_helpers.h"
#include "elaborator/nexttime_index.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

using NameSet = std::unordered_set<std::string_view>;

// The module's named sequences and properties by name, the diagnostics sink,
// and the declarations whose instance is being followed, so a cyclic
// instantiation, which §16.8 makes illegal on its own account, ends the walk.
struct BoundEnv {
  const NamedDecls& decls;
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
// integer literal, negated or not, is the parser's to check.
struct BoundScope {
  const ScopeMap& values;
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

// A bound's value: the expression's folded, else the literal's, `$` having
// none.
std::optional<int64_t> Fold(const Expr* e, uint32_t value,
                            const BoundScope& scope) {
  if (e != nullptr || value == SeqCycleDelay::kUnbounded) {
    return ConstEvalInt(e, scope.values);
  }
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

// §16.12.10: the index of nexttime and s_nexttime is a non-negative integer
// constant expression.
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

// §16.12.11 and §16.12.13: the bounds of a ranged always or eventually are
// non-negative integer constant expressions, the minimum no greater than
// the maximum. A `$` maximum is the parser's to judge, so it is read here as
// one a weak operator allows.
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

// The references to a formal in a declaration: all of them, and those §16.8
// lets a `$` actual reach, a range's upper bound and an instance's actual
// argument written whole.
struct References {
  int all = 0;
  int permitted = 0;
};

void CountIn(const Expr* e, std::string_view name, References& refs) {
  ForEachSubExpr(e, [&](const Expr* sub) {
    refs.all += static_cast<int>(IsNameRef(sub, name));
    if (sub->kind != ExprKind::kCall) return;
    for (const Expr* arg : sub->args) {
      refs.permitted += static_cast<int>(IsNameRef(arg, name));
    }
  });
}

// The bounds of a cycle delay or a repetition, `##d` and `[*d]` standing for
// the range [d:d], whose lower bound d is.
void CountBounds(const SeqCycleDelay& bounds, std::string_view name,
                 References& refs) {
  CountIn(bounds.min_expr, name, refs);
  if (bounds.max_expr == bounds.min_expr) return;
  CountIn(bounds.max_expr, name, refs);
  refs.permitted += static_cast<int>(IsNameRef(bounds.max_expr, name));
}

void CountBody(const SeqLinearBody& body, std::string_view name,
               References& refs) {
  ForEachBody(body, [&](const SeqLinearBody& b) {
    for (const SeqCycleDelay& delay : b.delays) CountBounds(delay, name, refs);
    for (const SeqRepetition& rep : b.repetitions) {
      CountBounds(rep, name, refs);
    }
  });
  ForEachBodyExpr(body, [&](const Expr* e) { CountIn(e, name, refs); });
}

// Whether the formal `i` of `decl` may be bound to `$`: untyped, and read
// only as a range's upper bound or as an instance's actual.
bool AdmitsDollar(const ModuleItem* decl, size_t i) {
  std::string_view name = decl->prop_formals[i];
  References refs;
  CountBody(decl->seq_linear, name, refs);
  CountIn(decl->prop_body_expr, name, refs);
  ForEachTreeNode(decl->prop_body_tree, [&](const PropertyExprNode& node) {
    CountIn(node.boolean, name, refs);
    CountIn(node.range_min, name, refs);
    CountIn(node.range_max, name, refs);
    if (node.sequence != nullptr) {
      CountBody(node.sequence->seq_linear, name, refs);
    }
  });
  return decl->prop_formal_type_kw[i] == TokenKind::kKwUntyped &&
         refs.all == refs.permitted;
}

// The actual bound to the formal `i` of `decl` by the instance `call`, or by
// the formal's default.
const Expr* ActualOf(const Expr* call, const ModuleItem* decl, size_t i) {
  const Expr* actual = i < call->args.size() ? call->args[i] : nullptr;
  return actual != nullptr ? actual : decl->prop_formal_defaults[i];
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
    if (!IsNameRef(ActualOf(call, decl, i), "$") || AdmitsDollar(decl, i))
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

// §16.7 and §16.8: an instance of a named sequence settles the bounds its
// declaration writes with a formal; they are checked with each formal bound
// to the instance's actual, folded in the scope the instance stands in.
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
  const BoundScope kInner{values, kFormals, true};
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

void CheckTree(const PropertyExprNode* node, const BoundScope& scope,
               BoundEnv& env) {
  ForEachTreeNode(node, [&](const PropertyExprNode& n) {
    using Kind = PropertyExprNode::Kind;
    if (n.kind == Kind::kNexttime) {
      CheckNexttime(n, scope, env.diag);
    } else if (n.kind == Kind::kAlways || n.kind == Kind::kEventually) {
      CheckRange(n, scope, env.diag);
    } else {
      CheckOperand(n.boolean, scope, env);
    }
    if (n.sequence != nullptr) CheckSequenceItem(n.sequence, scope, env);
  });
}

}  // namespace

void ValidateAssertionBoundRules(const ModuleDecl* decl, const ScopeMap& params,
                                 DiagEngine& diag) {
  const NamedDecls kNamed = NamedDeclsByName(decl, true);
  BoundEnv env{kNamed, diag, {}};
  for (const ModuleItem* item : decl->items) {
    if (kNamed.count(item->name) == 0) continue;
    const NameSet kFormals(item->prop_formals.begin(),
                           item->prop_formals.end());
    const BoundScope kOwn{params, kFormals, false};
    CheckSequenceItem(item, kOwn, env);
    CheckTree(item->prop_body_tree, kOwn, env);
  }
  const NameSet kNone;
  const BoundScope kModule{params, kNone, false};
  ForEachConcurrentAssertion(decl, [&](const Stmt* s) {
    CheckTree(s->assert_property, kModule, env);
    if (s->assert_sequence != nullptr) {
      CheckSequenceItem(s->assert_sequence, kModule, env);
    }
  });
}

}  // namespace delta
