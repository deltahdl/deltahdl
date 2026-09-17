#include <cstddef>
#include <cstdint>
#include <random>
#include <string>
#include <unordered_map>
#include <vector>

#include "simulator/constraint_solver.h"
#include "simulator/constraint_solver_internal.h"

namespace delta {

namespace {

// The domain of `var` narrowed by the comparison `sub`, its bounds folded
// as a comparison against a constant folds them before the draw.
RandVariable Narrowed(const RandVariable& var, const ConstraintExpr& sub) {
  RandVariable narrowed = var;
  auto above = [&](int64_t c) {
    narrowed.min_val = narrowed.DomainMax(narrowed.min_val, c);
  };
  auto below = [&](int64_t c) {
    narrowed.max_val = narrowed.DomainMin(narrowed.max_val, c);
  };
  switch (sub.kind) {
    case ConstraintKind::kGreaterEqual:
      above(sub.lo);
      break;
    case ConstraintKind::kGreaterThan:
      above(static_cast<int64_t>(static_cast<uint64_t>(sub.lo) + 1));
      break;
    case ConstraintKind::kLessEqual:
      below(sub.lo);
      break;
    case ConstraintKind::kLessThan:
      below(static_cast<int64_t>(static_cast<uint64_t>(sub.lo) - 1));
      break;
    case ConstraintKind::kRange:
      above(sub.lo);
      below(sub.hi);
      break;
    default:
      break;
  }
  return narrowed;
}

bool IsComparison(ConstraintKind kind) {
  return kind == ConstraintKind::kGreaterEqual ||
         kind == ConstraintKind::kGreaterThan ||
         kind == ConstraintKind::kLessEqual ||
         kind == ConstraintKind::kLessThan || kind == ConstraintKind::kRange;
}

}  // namespace

void ConstraintSolver::RepairConstraints(
    const std::vector<ConstraintExpr>& extra) {
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) RepairConstraint(c);
  }
  for (const auto& c : extra) RepairConstraint(c);
}

void ConstraintSolver::RepairConstraint(const ConstraintExpr& c) {
  if (c.kind == ConstraintKind::kCustom) {
    ApplyCustomRepair(c);
    return;
  }
  if (c.kind == ConstraintKind::kForeach) {
    size_t count =
        ClampCountToSize(c.sub_constraints.size(), c.size_var, values_);
    for (size_t i = 0; i < count; ++i) RepairConstraint(c.sub_constraints[i]);
    return;
  }
  if (c.kind != ConstraintKind::kImplication || !c.cond_fn ||
      !c.cond_fn(values_)) {
    return;
  }
  for (const ConstraintExpr& sub : c.sub_constraints) RepairConsequent(sub);
}

void ConstraintSolver::RepairConsequent(const ConstraintExpr& sub) {
  if (sub.kind == ConstraintKind::kCustom ||
      sub.kind == ConstraintKind::kImplication) {
    RepairConstraint(sub);
    return;
  }
  if (EvalConstraint(sub) || !RepairMayWrite(sub.var_name)) return;
  auto it = variables_.find(sub.var_name);
  if (sub.kind == ConstraintKind::kEqual) {
    values_[sub.var_name] = sub.lo;
  } else if (sub.kind == ConstraintKind::kSetMembership) {
    if (sub.set_values.empty()) return;
    std::uniform_int_distribution<size_t> pick(0, sub.set_values.size() - 1);
    values_[sub.var_name] = sub.set_values[pick(rng_)];
  } else if (IsComparison(sub.kind)) {
    RandVariable narrowed = Narrowed(it->second, sub);
    if (narrowed.min_val > narrowed.max_val) return;
    values_[sub.var_name] = GenerateRandValue(narrowed);
  }
}

// The structured candidates of a variable's domain: 0, each power of two the
// width holds and its two neighbours, the bounds, and, where the domain is
// signed, the negatives of the powers.
std::vector<int64_t> StructuredCandidates(const RandVariable& var) {
  std::vector<int64_t> out{0, var.min_val, var.max_val};
  for (uint32_t i = 0; i < var.width && i < 63; ++i) {
    auto power = static_cast<int64_t>(uint64_t{1} << i);
    out.push_back(power);
    out.push_back(power - 1);
    out.push_back(power + 1);
    if (var.is_signed) out.push_back(-power);
  }
  return out;
}

// Whether the variable `name` is one a repair may write: one the solver
// holds, active, integral and, 18.4.2, not randc, which is drawn from its
// own cycle alone, and, 18.8, holding no state value, which is never
// written.
bool ConstraintSolver::RepairMayWrite(const std::string& name) const {
  if (HoldsStateValue(name)) return false;
  auto it = variables_.find(name);
  return it != variables_.end() && it->second.enabled && !it->second.is_real &&
         it->second.qualifier != RandQualifier::kRandc;
}

void ConstraintSolver::RepairFromCandidates(const ConstraintExpr& c) {
  const std::string& name = c.ref_vars[0];
  const RandVariable& var = variables_.find(name)->second;
  std::vector<int64_t> satisfying;
  std::unordered_map<std::string, int64_t> trial = values_;
  for (int64_t candidate : StructuredCandidates(var)) {
    if (candidate < var.min_val || candidate > var.max_val) continue;
    trial[name] = candidate;
    if (c.eval_fn(trial)) satisfying.push_back(candidate);
  }
  if (satisfying.empty()) return;
  std::uniform_int_distribution<size_t> pick(0, satisfying.size() - 1);
  values_[name] = satisfying[pick(rng_)];
}

// The derived variable written from the others: the value the expression
// takes where the relation is an equality, and a fresh draw from its domain
// narrowed by the bound the expression gives it under any other comparison.
void ConstraintSolver::ApplyDerived(const ConstraintExpr& c) {
  if (!RepairMayWrite(c.var_name)) return;
  int64_t derived = c.derive_fn(values_);
  if (c.derive_cmp == ConstraintKind::kEqual) {
    values_[c.var_name] = derived;
    return;
  }
  ConstraintExpr bound;
  bound.kind = c.derive_cmp;
  bound.lo = derived;
  RandVariable narrowed = Narrowed(variables_.find(c.var_name)->second, bound);
  if (narrowed.min_val > narrowed.max_val) return;
  values_[c.var_name] = GenerateRandValue(narrowed);
}

void ConstraintSolver::ApplyCustomRepair(const ConstraintExpr& c) {
  if (c.kind != ConstraintKind::kCustom || !c.eval_fn || c.eval_fn(values_)) {
    return;
  }
  if (c.derive_fn) {
    ApplyDerived(c);
    return;
  }
  if (c.ref_vars.size() == 1 && RepairMayWrite(c.ref_vars[0])) {
    RepairFromCandidates(c);
  }
}

}  // namespace delta
