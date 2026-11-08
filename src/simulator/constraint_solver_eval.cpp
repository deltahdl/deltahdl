#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "simulator/constraint_solver.h"
#include "simulator/constraint_solver_internal.h"

namespace delta {

static bool EvalRange(bool is_signed, int64_t val, int64_t lo, int64_t hi) {
  return !ValueLess(is_signed, val, lo) && !ValueLess(is_signed, hi, val);
}

static bool EvalSetMembership(int64_t val,
                              const std::vector<int64_t>& set_values) {
  for (int64_t v : set_values) {
    if (val == v) return true;
  }
  return false;
}

static bool EvalComparison(ConstraintKind kind, bool is_signed, int64_t val,
                           int64_t target) {
  switch (kind) {
    case ConstraintKind::kEqual:
      return val == target;
    case ConstraintKind::kNotEqual:
      return val != target;
    case ConstraintKind::kLessThan:
      return ValueLess(is_signed, val, target);
    case ConstraintKind::kGreaterThan:
      return ValueLess(is_signed, target, val);
    case ConstraintKind::kLessEqual:
      return !ValueLess(is_signed, target, val);
    case ConstraintKind::kGreaterEqual:
      return !ValueLess(is_signed, val, target);
    default:
      return true;
  }
}

bool ConstraintSolver::DeclaredSigned(const std::string& name) const {
  auto it = variables_.find(name);
  return it == variables_.end() || it->second.is_signed;
}

bool ConstraintSolver::EvalConstraint(const ConstraintExpr& expr) const {
  switch (expr.kind) {
    case ConstraintKind::kRange: {
      auto it = values_.find(expr.var_name);
      if (it == values_.end()) return true;
      return EvalRange(DeclaredSigned(expr.var_name), it->second, expr.lo,
                       expr.hi);
    }
    case ConstraintKind::kSetMembership: {
      auto it = values_.find(expr.var_name);
      if (it == values_.end()) return true;
      return EvalSetMembership(it->second, expr.set_values);
    }
    case ConstraintKind::kEqual:
    case ConstraintKind::kNotEqual:
    case ConstraintKind::kLessThan:
    case ConstraintKind::kGreaterThan:
    case ConstraintKind::kLessEqual:
    case ConstraintKind::kGreaterEqual: {
      auto it = values_.find(expr.var_name);
      if (it == values_.end()) return true;
      return EvalComparison(expr.kind, DeclaredSigned(expr.var_name),
                            it->second, expr.lo);
    }
    case ConstraintKind::kImplication:
      return EvalImplication(expr);
    case ConstraintKind::kIfElse:
      return EvalIfElse(expr);
    case ConstraintKind::kForeach:
      return EvalForeach(expr);
    case ConstraintKind::kArrayReduction:
      return EvalArrayReduction(expr);
    case ConstraintKind::kUnique:
      return EvalUnique(expr);
    case ConstraintKind::kDist:
    case ConstraintKind::kSoft:
    case ConstraintKind::kDisableSoft:

      return true;
    case ConstraintKind::kCustom:
      return expr.eval_fn ? expr.eval_fn(values_) : true;
  }
  return true;
}

bool ConstraintSolver::ApplyConstraint(const ConstraintExpr& expr) {
  if (expr.kind == ConstraintKind::kDist) {
    SeedDist(expr, {});
    return true;
  }
  return EvalConstraint(expr);
}

void CollectConstraints(const std::vector<ConstraintBlock>& blocks,
                        const std::vector<ConstraintExpr>& extra,
                        std::vector<const ConstraintExpr*>& hard,
                        std::vector<const ConstraintExpr*>& soft) {
  auto classify = [&](const ConstraintExpr& c) {
    if (c.kind == ConstraintKind::kDisableSoft) return;
    if (c.kind == ConstraintKind::kSoft) {
      soft.push_back(&c);
    } else {
      hard.push_back(&c);
    }
  };
  for (const auto& block : blocks) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) classify(c);
  }
  for (const auto& c : extra) classify(c);
}

namespace {

enum class GuardCheckResult : std::uint8_t { kFail, kSkip, kProceed };

GuardCheckResult ResolveConstraintGuard(
    const ConstraintExpr& c,
    const std::unordered_map<std::string, int64_t>& values, bool& guard_error) {
  if (!c.has_guard) return GuardCheckResult::kProceed;
  switch (GuardFinalOutcome(EvaluateGuard(c.guard, values))) {
    case GuardOutcome::kError:
      guard_error = true;
      return GuardCheckResult::kFail;
    case GuardOutcome::kEliminated:
      return GuardCheckResult::kSkip;
    case GuardOutcome::kUnconditional:
    case GuardOutcome::kConditional:
      break;
  }
  return GuardCheckResult::kProceed;
}

bool CheckActiveSoftConstraints(
    const std::vector<const ConstraintExpr*>& soft,
    const std::unordered_set<const ConstraintExpr*>& dropped_soft,
    const std::unordered_set<const ConstraintExpr*>& disabled_soft,
    const std::function<bool(const ConstraintExpr&)>& eval) {
  for (const auto* c : soft) {
    if (dropped_soft.count(c) || disabled_soft.count(c)) continue;
    const ConstraintExpr* inner = c->inner ? c->inner : nullptr;
    if (inner && !eval(*inner)) return false;
  }
  return true;
}

}  // namespace

bool ConstraintSolver::CheckAllConstraints(
    const std::vector<ConstraintExpr>& extra, bool include_soft) {
  std::vector<const ConstraintExpr*> hard;
  std::vector<const ConstraintExpr*> soft;
  CollectConstraints(blocks_, extra, hard, soft);
  for (const auto* c : hard) {
    switch (ResolveConstraintGuard(*c, values_, guard_error_)) {
      case GuardCheckResult::kFail:
        return false;
      case GuardCheckResult::kSkip:
        continue;
      case GuardCheckResult::kProceed:
        break;
    }
    if (!EvalConstraint(*c)) return false;
  }
  return !include_soft ||
         CheckActiveSoftConstraints(
             soft, dropped_soft_, disabled_soft_,
             [this](const ConstraintExpr& e) { return EvalConstraint(e); });
}

bool ConstraintSolver::EvalImplication(const ConstraintExpr& expr) const {
  bool antecedent = false;
  if (expr.cond_fn) {
    antecedent = expr.cond_fn(values_);
  } else {
    auto it = values_.find(expr.cond_var);
    if (it == values_.end()) return true;
    antecedent = (it->second == expr.cond_value);
  }
  if (!antecedent) return true;
  for (const auto& sub : expr.sub_constraints) {
    if (!EvalConstraint(sub)) return false;
  }
  return true;
}

bool ConstraintSolver::EvalIfElse(const ConstraintExpr& expr) const {
  bool cond = false;
  if (expr.cond_fn) {
    cond = expr.cond_fn(values_);
  } else {
    auto it = values_.find(expr.cond_var);
    if (it == values_.end()) return true;
    cond = (it->second == expr.cond_value);
  }
  const auto& branch = cond ? expr.sub_constraints : expr.else_constraints;
  for (const auto& sub : branch) {
    if (!EvalConstraint(sub)) return false;
  }
  return true;
}

bool ConstraintSolver::EvalForeach(const ConstraintExpr& expr) const {
  size_t count =
      ClampCountToSize(expr.sub_constraints.size(), expr.size_var, values_);
  for (size_t i = 0; i < count; ++i) {
    if (!EvalConstraint(expr.sub_constraints[i])) return false;
  }
  return true;
}

namespace {

int64_t ReductionIdentity(ArrayReductionOp op) {
  switch (op) {
    case ArrayReductionOp::kSum:
    case ArrayReductionOp::kOr:
    case ArrayReductionOp::kXor:
      return 0;
    case ArrayReductionOp::kProduct:
      return 1;
    case ArrayReductionOp::kAnd:
      return -1;
  }
  return 0;
}

int64_t FoldReductionElement(ArrayReductionOp op, int64_t acc, int64_t v) {
  switch (op) {
    case ArrayReductionOp::kSum:
      return acc + v;
    case ArrayReductionOp::kProduct:
      return acc * v;
    case ArrayReductionOp::kAnd:
      return acc & v;
    case ArrayReductionOp::kOr:
      return acc | v;
    case ArrayReductionOp::kXor:
      return acc ^ v;
  }
  return acc;
}

}  // namespace

size_t ClampCountToSize(
    size_t count, const std::string& size_var,
    const std::unordered_map<std::string, int64_t>& values) {
  if (size_var.empty()) return count;
  auto sit = values.find(size_var);
  if (sit == values.end()) return count;
  int64_t sz = sit->second < 0 ? 0 : sit->second;
  if (static_cast<size_t>(sz) < count) return static_cast<size_t>(sz);
  return count;
}

int64_t ConstraintSolver::FoldReduction(const ConstraintExpr& expr) const {
  int64_t acc = ReductionIdentity(expr.reduce_op);

  size_t count =
      ClampCountToSize(expr.reduce_vars.size(), expr.size_var, values_);

  for (size_t i = 0; i < count; ++i) {
    auto it = values_.find(expr.reduce_vars[i]);
    if (it == values_.end()) continue;
    int64_t v = expr.reduce_with ? expr.reduce_with(it->second) : it->second;
    acc = FoldReductionElement(expr.reduce_op, acc, v);
  }

  if (expr.reduce_width > 0 && expr.reduce_width < 64) {
    uint64_t mask = (static_cast<uint64_t>(1) << expr.reduce_width) - 1;
    acc = static_cast<int64_t>(static_cast<uint64_t>(acc) & mask);
  }
  return acc;
}

bool ConstraintSolver::EvalArrayReduction(const ConstraintExpr& expr) const {
  return EvalComparison(expr.reduce_cmp, true, FoldReduction(expr), expr.lo);
}

bool ConstraintSolver::EvalUnique(const ConstraintExpr& expr) const {
  std::unordered_set<int64_t> seen;
  std::unordered_set<double> seen_real;
  for (const auto& vname : expr.unique_vars) {
    auto rt = real_values_.find(vname);
    if (rt != real_values_.end()) {
      if (!seen_real.insert(rt->second).second) return false;
      continue;
    }
    auto it = values_.find(vname);
    if (it == values_.end()) continue;
    if (!seen.insert(it->second).second) return false;
  }
  return true;
}

}  // namespace delta
