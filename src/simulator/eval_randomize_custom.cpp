#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

void SetLocalWords(Logic4Vec& value, int64_t v) {
  if (value.nwords == 0) return;
  auto bits = static_cast<uint64_t>(v);
  if (value.width < 64) bits &= (uint64_t{1} << value.width) - 1;
  value.words[0].aval = bits;
  value.words[0].bval = 0;
}

namespace {

Variable* TrialLocal(const std::string& n, bool real, RandomizeCtx& rc) {
  auto it = rc.trial_locals.find(n);
  if (it != rc.trial_locals.end()) {
    rc.ctx.BindLocalVariable(n, it->second);
    return it->second;
  }
  const RandVariable* var = rc.solver != nullptr && !real
                                ? rc.solver->FindVariable(rc.solver_prefix + n)
                                : nullptr;
  uint32_t width = real ? 64 : var != nullptr ? std::max(var->width, 32u) : 32;
  bool is_signed = !real && (var == nullptr || var->is_signed);
  Variable* local = rc.ctx.CreateLocalVariable(n, width, is_signed);
  rc.trial_locals[n] = local;
  return local;
}

Logic4Vec EvalBound(const Expr* e, const std::vector<std::string>& names,
                    RandomizeCtx& rc,
                    const std::unordered_map<std::string, int64_t>& vals) {
  rc.ctx.PushScope();
  for (const auto& n : names) {
    auto it = vals.find(n);
    bool real = rc.solver != nullptr &&
                rc.solver->FindVariable(rc.solver_prefix + n)->is_real;
    Variable* local = TrialLocal(n, real, rc);
    if (real) {
      local->value = MakeRealVec(
          rc.arena, rc.solver->GetRealValue(rc.solver_prefix + n), 64);
      continue;
    }
    SetLocalWords(local->value, it != vals.end() ? it->second : 0);
  }
  Logic4Vec value;
  {
    ConstraintEvalScope scope(rc.obj, rc.ctx);
    value = EvalExpr(e, rc.ctx, rc.arena);
  }
  rc.ctx.PopScope();
  return value;
}

bool RandIsActive(const RandomizeCtx& rc, std::string_view name) {
  return rc.obj == nullptr || IsObjectRandActive(rc.obj, name);
}

const Expr* DerivedSide(const Expr* rel, std::vector<RandInfo>& rands,
                        RandomizeCtx& rc, ConstraintKind& cmp) {
  if (rel->kind != ExprKind::kBinary || rel->lhs == nullptr ||
      rel->rhs == nullptr || rel->op == TokenKind::kBangEq ||
      !ComparisonKind(rel->op, cmp)) {
    return nullptr;
  }
  for (const Expr* side : {rel->lhs, rel->rhs}) {
    const Expr* other = side == rel->lhs ? rel->rhs : rel->lhs;
    if (side->kind == ExprKind::kIdentifier &&
        FindRand(rands, side->text) != nullptr &&
        RandIsActive(rc, side->text) && !RefsNamedRandVar(other, side->text)) {
      if (side == rel->rhs) ComparisonKind(MirrorComparison(rel->op), cmp);
      return side;
    }
  }
  return nullptr;
}

const Expr* AddendOf(const Expr* side, std::vector<RandInfo>& rands,
                     RandomizeCtx& rc, const Expr*& term, bool& subtrahend) {
  if (side->kind != ExprKind::kBinary || side->lhs == nullptr ||
      side->rhs == nullptr ||
      (side->op != TokenKind::kPlus && side->op != TokenKind::kMinus)) {
    return nullptr;
  }
  for (const Expr* x : {side->lhs, side->rhs}) {
    const Expr* q = x == side->lhs ? side->rhs : side->lhs;
    if (x->kind != ExprKind::kIdentifier ||
        FindRand(rands, x->text) == nullptr || !RandIsActive(rc, x->text) ||
        RefsNamedRandVar(q, x->text)) {
      continue;
    }
    term = q;
    subtrahend = side->op == TokenKind::kMinus && x == side->rhs;
    return x;
  }
  return nullptr;
}

const Expr* AddendSide(const Expr* rel, std::vector<RandInfo>& rands,
                       RandomizeCtx& rc, const Expr*& term, bool& subtrahend) {
  ConstraintKind cmp = ConstraintKind::kEqual;
  if (rel->kind != ExprKind::kBinary || rel->lhs == nullptr ||
      rel->rhs == nullptr || rel->op == TokenKind::kBangEq ||
      !ComparisonKind(rel->op, cmp)) {
    return nullptr;
  }
  for (const Expr* side : {rel->lhs, rel->rhs}) {
    const Expr* other = side == rel->lhs ? rel->rhs : rel->lhs;
    const Expr* x = AddendOf(side, rands, rc, term, subtrahend);
    if (x != nullptr && !RefsNamedRandVar(other, x->text)) return side;
  }
  return nullptr;
}

}  // namespace

int64_t HeldToVariable(int64_t v, const std::string& name, RandomizeCtx& rc) {
  const RandVariable* var =
      rc.solver != nullptr ? rc.solver->FindVariable(rc.solver_prefix + name)
                           : nullptr;
  if (var == nullptr || var->width >= 64) return v;
  auto bits = static_cast<uint64_t>(v) & ((uint64_t{1} << var->width) - 1);
  return var->is_signed ? SignExtend(bits, var->width)
                        : static_cast<int64_t>(bits);
}

namespace {

bool DeriveAddend(const Expr* rel, std::vector<RandInfo>& rands,
                  const std::vector<std::string>& names, RandomizeCtx& rc,
                  ConstraintExpr& ce) {
  const Expr* term = nullptr;
  bool subtrahend = false;
  const Expr* side = AddendSide(rel, rands, rc, term, subtrahend);
  if (side == nullptr) return false;
  const Expr* x = term == side->lhs ? side->rhs : side->lhs;
  const Expr* other = side == rel->lhs ? rel->rhs : rel->lhs;
  TokenKind op = side == rel->rhs ? MirrorComparison(rel->op) : rel->op;
  if (subtrahend) op = MirrorComparison(op);
  ce.var_name = std::string(x->text);
  ComparisonKind(op, ce.derive_cmp);
  bool subtract_term = side->op == TokenKind::kPlus;
  ce.derive_fn = [other, term, subtrahend, subtract_term, names,
                  name = ce.var_name,
                  &rc](const std::unordered_map<std::string, int64_t>& vals) {
    int64_t o = EvalCustomValue(other, names, rc, vals);
    int64_t q = EvalCustomValue(term, names, rc, vals);
    int64_t derived = subtrahend ? q - o : subtract_term ? o - q : o + q;
    return HeldToVariable(derived, name, rc);
  };
  return true;
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
  ConstraintKind cmp = ConstraintKind::kEqual;
  if (const Expr* derived = DerivedSide(rel, rands, rc, cmp)) {
    const Expr* other = derived == rel->lhs ? rel->rhs : rel->lhs;
    ce.var_name = std::string(derived->text);
    ce.derive_cmp = cmp;
    ce.derive_fn = [other, names,
                    &rc](const std::unordered_map<std::string, int64_t>& vals) {
      return EvalCustomValue(other, names, rc, vals);
    };
    if (other->kind == ExprKind::kIdentifier &&
        FindRand(rands, other->text) != nullptr) {
      ce.co_var_name = std::string(other->text);
    }
    return ce;
  }
  DeriveAddend(rel, rands, names, rc, ce);
  return ce;
}

}  // namespace delta
