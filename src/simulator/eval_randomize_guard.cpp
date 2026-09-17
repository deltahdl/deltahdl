#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>

#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// 18.5.12: whether the property `name` of the class `type`, or of one it
// inherits from, is declared of a class type, so the value it holds is an
// object handle.
bool IsClassTypedProperty(const ClassTypeInfo* type, std::string_view name,
                          SimContext& ctx) {
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    for (const auto& p : lvl->properties) {
      if (p.name != name) continue;
      return !p.type_name.empty() && ctx.FindClassType(p.type_name) != nullptr;
    }
  }
  return false;
}

bool HandleValue(const Expr* h, ClassObject* owner, RandomizeCtx& rc,
                 uint64_t& out);

// The handle the member access `h` names, `g.h` over the handle expression
// `g`, read into `out`: a class-typed property of the object `g` names, or
// of `owner` where `g` is this. Answers false where it names no handle,
// and where `g` is null, which the dereference of `g` reports.
bool MemberHandleValue(const Expr* h, ClassObject* owner, RandomizeCtx& rc,
                       uint64_t& out) {
  if (h->lhs == nullptr || h->rhs == nullptr ||
      h->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (h->lhs->kind == ExprKind::kIdentifier && h->lhs->text == "this")
    return HandleValue(h->rhs, owner, rc, out);
  uint64_t through = kNullClassHandle;
  if (!HandleValue(h->lhs, owner, rc, through)) return false;
  ClassObject* obj = rc.ctx.GetClassObject(through);
  if (obj == nullptr || !IsClassTypedProperty(obj->type, h->rhs->text, rc.ctx))
    return false;
  out = obj->GetProperty(h->rhs->text, rc.arena).ToUint64();
  return true;
}

// The handle the expression `h` names, read into `out`: a class-typed
// property of `owner`, bare or as this.h; a class-typed variable; or a
// class-typed property of the object a handle expression names, `g.h`.
// Answers false where `h` names no handle, and where it is reached through
// a null handle, which the dereference of that handle reports.
bool HandleValue(const Expr* h, ClassObject* owner, RandomizeCtx& rc,
                 uint64_t& out) {
  if (h == nullptr) return false;
  if (h->kind == ExprKind::kMemberAccess && !h->is_scope_resolution)
    return MemberHandleValue(h, owner, rc, out);
  if (h->kind != ExprKind::kIdentifier) return false;
  if (owner != nullptr && IsClassTypedProperty(owner->type, h->text, rc.ctx)) {
    out = owner->GetProperty(h->text, rc.arena).ToUint64();
    return true;
  }
  if (rc.ctx.GetVariableClassType(h->text).empty()) return false;
  const Variable* var = rc.ctx.FindVariable(h->text);
  if (var == nullptr) return false;
  out = var->value.ToUint64();
  return true;
}

// 18.5.12: whether evaluating `e` reads a member through a null handle, the
// evaluation error a guard exists to sift away.
bool DereferencesNull(const Expr* e, ClassObject* owner, RandomizeCtx& rc) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution) {
    uint64_t handle = kNullClassHandle;
    if (HandleValue(e->lhs, owner, rc, handle) && handle == kNullClassHandle)
      return true;
  }
  for (const Expr* sub : {e->lhs, e->rhs, e->base, e->index, e->index_end,
                          e->condition, e->true_expr, e->false_expr}) {
    if (DereferencesNull(sub, owner, rc)) return true;
  }
  for (const Expr* sub : e->args) {
    if (DereferencesNull(sub, owner, rc)) return true;
  }
  for (const Expr* sub : e->elements) {
    if (DereferencesNull(sub, owner, rc)) return true;
  }
  return false;
}

// 18.5.12: the four-state value of the guard subexpression `e`, free of
// random variables: ERROR where it reads through a null handle, and
// otherwise the truth of its value over the state variables, evaluated in
// the scope of the object whose constraint it guards.
GuardValue EvalGuardLeaf(const Expr* e, ClassObject* owner, RandomizeCtx& rc) {
  if (DereferencesNull(e, owner, rc)) return GuardValue::kError;
  rc.ctx.PushScope();
  Logic4Vec value;
  {
    ConstraintEvalScope scope(owner, rc.ctx);
    value = EvalExpr(e, rc.ctx, rc.arena);
  }
  rc.ctx.PopScope();
  return value.IsTruthy() ? GuardValue::kTrue : GuardValue::kFalse;
}

// 18.5.12: the guard predicate of the antecedent `e`: a conjunction,
// disjunction or negation over the predicates of its operands, and any
// other expression a leaf, RANDOM where it involves a random variable, which
// cannot be evaluated before the solve, and otherwise evaluated over the
// state when the guard is resolved, which is after pre_randomize() has run.
GuardPredicate BuildGuardPredicate(
    const Expr* e, const std::function<bool(const Expr*)>& refs_rand,
    ClassObject* owner, RandomizeCtx& rc) {
  GuardPredicate pred;
  if (e != nullptr && e->kind == ExprKind::kBinary &&
      (e->op == TokenKind::kAmpAmp || e->op == TokenKind::kPipePipe) &&
      e->lhs != nullptr && e->rhs != nullptr) {
    pred.op = e->op == TokenKind::kAmpAmp ? GuardPredicate::Op::kAnd
                                          : GuardPredicate::Op::kOr;
    pred.operands.push_back(BuildGuardPredicate(e->lhs, refs_rand, owner, rc));
    pred.operands.push_back(BuildGuardPredicate(e->rhs, refs_rand, owner, rc));
    return pred;
  }
  if (e != nullptr && e->kind == ExprKind::kUnary &&
      e->op == TokenKind::kBang && e->lhs != nullptr) {
    pred.op = GuardPredicate::Op::kNot;
    pred.operands.push_back(BuildGuardPredicate(e->lhs, refs_rand, owner, rc));
    return pred;
  }
  if (refs_rand(e)) {
    pred.leaf_fn = [](const std::unordered_map<std::string, int64_t>&) {
      return GuardValue::kRandom;
    };
    return pred;
  }
  pred.leaf_fn = [e, owner,
                  &rc](const std::unordered_map<std::string, int64_t>&) {
    return EvalGuardLeaf(e, owner, rc);
  };
  return pred;
}

}  // namespace

void AttachConstraintGuard(const Expr* rel,
                           const std::function<bool(const Expr*)>& refs_rand,
                           ClassObject* owner, RandomizeCtx& rc,
                           ConstraintExpr& out) {
  if (rel == nullptr || rel->kind != ExprKind::kBinary ||
      rel->op != TokenKind::kArrow || rel->lhs == nullptr) {
    return;
  }
  out.has_guard = true;
  out.guard = BuildGuardPredicate(rel->lhs, refs_rand, owner, rc);
}

}  // namespace delta
