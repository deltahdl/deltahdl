#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// Evaluates `e` with each name in `names` bound to its value in `vals`, a
// rand variable as a local so the expression reads the trial value. A name
// `vals` lacks is a real variable's (18.4.1), whose draw the solver keeps
// among its real values, so the local is the real drawn there and an
// expression over it reads the real (18.5.5).
Logic4Vec EvalBound(const Expr* e, const std::vector<std::string>& names,
                    RandomizeCtx& rc,
                    const std::unordered_map<std::string, int64_t>& vals) {
  rc.ctx.PushScope();
  for (const auto& n : names) {
    auto it = vals.find(n);
    if (it == vals.end() && rc.solver != nullptr) {
      rc.ctx.CreateLocalVariable(n, 64)->value =
          MakeRealVec(rc.arena, rc.solver->GetRealValue(n), 64);
      continue;
    }
    int64_t v = it != vals.end() ? it->second : 0;
    rc.ctx.CreateLocalVariable(n, 32)->value =
        MakeLogic4VecVal(rc.arena, 32, static_cast<uint64_t>(v));
  }
  Logic4Vec value;
  {
    ConstraintEvalScope scope(rc.obj, rc.ctx);
    value = EvalExpr(e, rc.ctx, rc.arena);
  }
  rc.ctx.PopScope();
  return value;
}

// The side of the equality `rel` that is a bare random variable the other
// side does not reference, so that the other side derives it; nullptr
// where neither side is.
const Expr* DerivedSide(const Expr* rel, std::vector<RandInfo>& rands) {
  if (rel->kind != ExprKind::kBinary || rel->op != TokenKind::kEqEq ||
      rel->lhs == nullptr || rel->rhs == nullptr) {
    return nullptr;
  }
  for (const Expr* side : {rel->lhs, rel->rhs}) {
    const Expr* other = side == rel->lhs ? rel->rhs : rel->lhs;
    if (side->kind == ExprKind::kIdentifier &&
        FindRand(rands, side->text) != nullptr &&
        !RefsNamedRandVar(other, side->text)) {
      return side;
    }
  }
  return nullptr;
}

}  // namespace

bool EvalCustomRelation(const Expr* rel, const std::vector<std::string>& names,
                        RandomizeCtx& rc,
                        const std::unordered_map<std::string, int64_t>& vals) {
  return EvalBound(rel, names, rc, vals).IsTruthy();
}

int64_t EvalCustomValue(const Expr* e, const std::vector<std::string>& names,
                        RandomizeCtx& rc,
                        const std::unordered_map<std::string, int64_t>& vals) {
  Logic4Vec value = EvalBound(e, names, rc, vals);
  return value.is_signed ? SignExtend(value.ToUint64(), value.width)
                         : static_cast<int64_t>(value.ToUint64());
}

bool RefsNamedRandVar(const Expr* e, std::string_view name) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) return e->text == name;
  if (e->kind == ExprKind::kMemberAccess) {
    return e->lhs != nullptr && e->lhs->kind == ExprKind::kIdentifier &&
           e->lhs->text == "this" && e->rhs != nullptr &&
           e->rhs->kind == ExprKind::kIdentifier && e->rhs->text == name;
  }
  for (const Expr* sub : {e->lhs, e->rhs, e->base, e->index, e->index_end,
                          e->condition, e->true_expr, e->false_expr}) {
    if (RefsNamedRandVar(sub, name)) return true;
  }
  for (const Expr* sub : e->args) {
    if (RefsNamedRandVar(sub, name)) return true;
  }
  for (const Expr* sub : e->elements) {
    if (RefsNamedRandVar(sub, name)) return true;
  }
  return false;
}

ConstraintExpr MakeCustomConstraint(const Expr* rel,
                                    std::vector<RandInfo>& rands,
                                    RandomizeCtx& rc) {
  std::vector<std::string> names;
  names.reserve(rands.size());
  for (const auto& ri : rands) names.push_back(ri.name);
  ConstraintExpr ce;
  ce.kind = ConstraintKind::kCustom;
  // 18.5.7: a relation naming an array member whole -- a reduction method
  // over it, or a select of it the expansion left as written -- references
  // each of its elements.
  for (const auto& ri : rands) {
    if (RefsNamedRandVar(rel, ri.name) ||
        (!ri.array_base.empty() && RefsNamedRandVar(rel, ri.array_base))) {
      ce.ref_vars.push_back(ri.name);
    }
  }
  ce.eval_fn = [rel, names,
                &rc](const std::unordered_map<std::string, int64_t>& vals) {
    return EvalCustomRelation(rel, names, rc, vals);
  };
  // 18.3: `x == expression` over the other random variables, the clause's
  // data == 1 << n, derives x from them once they are drawn.
  if (const Expr* derived = DerivedSide(rel, rands)) {
    const Expr* other = derived == rel->lhs ? rel->rhs : rel->lhs;
    ce.var_name = std::string(derived->text);
    ce.derive_fn = [other, names,
                    &rc](const std::unordered_map<std::string, int64_t>& vals) {
      return EvalCustomValue(other, names, rc, vals);
    };
  }
  return ce;
}

}  // namespace delta
