#include <cstddef>
#include <cstdint>
#include <random>
#include <string>
#include <unordered_map>
#include <vector>

#include "simulator/constraint_solver.h"

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

void ConstraintSolver::RepairConditionalConstraints(
    const std::vector<ConstraintExpr>& extra) {
  auto visit = [&](const ConstraintExpr& c) {
    if (c.kind != ConstraintKind::kImplication || !c.cond_fn ||
        !c.cond_fn(values_)) {
      return;
    }
    for (const ConstraintExpr& sub : c.sub_constraints) ApplyConsequent(sub);
  };
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) visit(c);
  }
  for (const auto& c : extra) visit(c);
}

void ConstraintSolver::ApplyConsequent(const ConstraintExpr& sub) {
  // 18.8: a variable holding a state value is never written, and 18.4.2 a
  // randc variable is drawn from its own cycle alone.
  if (HoldsStateValue(sub.var_name) || EvalConstraint(sub)) return;
  auto it = variables_.find(sub.var_name);
  if (it == variables_.end() || !it->second.enabled || it->second.is_real ||
      it->second.qualifier == RandQualifier::kRandc) {
    return;
  }
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
    int64_t power = static_cast<int64_t>(uint64_t{1} << i);
    out.push_back(power);
    out.push_back(power - 1);
    out.push_back(power + 1);
    if (var.is_signed) out.push_back(-power);
  }
  return out;
}

void ConstraintSolver::RepairCustomConstraints(
    const std::vector<ConstraintExpr>& extra) {
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) ApplyCustomRepair(c);
  }
  for (const auto& c : extra) ApplyCustomRepair(c);
}

void ConstraintSolver::ApplyCustomRepair(const ConstraintExpr& c) {
  if (c.kind != ConstraintKind::kCustom || !c.eval_fn || c.eval_fn(values_)) {
    return;
  }
  if (c.derive_fn) {
    if (HoldsStateValue(c.var_name)) return;
    auto it = variables_.find(c.var_name);
    if (it == variables_.end() || !it->second.enabled ||
        it->second.qualifier == RandQualifier::kRandc) {
      return;
    }
    values_[c.var_name] = c.derive_fn(values_);
    return;
  }
  if (c.ref_vars.size() != 1 || HoldsStateValue(c.ref_vars[0])) return;
  auto it = variables_.find(c.ref_vars[0]);
  if (it == variables_.end() || !it->second.enabled || it->second.is_real ||
      it->second.qualifier == RandQualifier::kRandc) {
    return;
  }
  const RandVariable& var = it->second;
  std::vector<int64_t> satisfying;
  std::unordered_map<std::string, int64_t> trial = values_;
  for (int64_t candidate : StructuredCandidates(var)) {
    if (candidate < var.min_val || candidate > var.max_val) continue;
    trial[c.ref_vars[0]] = candidate;
    if (c.eval_fn(trial)) satisfying.push_back(candidate);
  }
  if (satisfying.empty()) return;
  std::uniform_int_distribution<size_t> pick(0, satisfying.size() - 1);
  values_[c.ref_vars[0]] = satisfying[pick(rng_)];
}

}  // namespace delta
