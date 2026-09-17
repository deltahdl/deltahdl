#include <algorithm>
#include <cstdint>
#include <functional>
#include <string>
#include <unordered_map>
#include <vector>

#include "simulator/constraint_solver.h"
#include "simulator/constraint_solver_internal.h"

namespace delta {

// 18.5.7.1: an array's size method is solved with the size constraints,
// ahead of the iterative (foreach) constraints over that array. The sizes
// are drawn once per solve, ahead of the attempts that solve the other
// variables, and held through them.

void DrawArraySizeVariables(
    std::unordered_map<std::string, RandVariable>& variables,
    std::unordered_map<std::string, int64_t>& values,
    const std::function<int64_t(RandVariable&)>& gen) {
  for (auto& [name, var] : variables) {
    if (!var.enabled || var.is_real) continue;
    if (!var.is_array_size) continue;
    if (var.qualifier == RandQualifier::kRandc) continue;
    if (values.find(name) != values.end()) continue;
    values[name] = gen(var);
  }
}

// 18.5.7.1: whether every hard constraint decided on an array size alone --
// a size constraint -- holds under the values drawn.
bool ConstraintSolver::SizeConstraintsHold(
    const std::vector<ConstraintExpr>& extra) {
  std::vector<const ConstraintExpr*> hard;
  std::vector<const ConstraintExpr*> soft;
  CollectConstraints(blocks_, extra, hard, soft);
  for (const auto& [name, var] : variables_) {
    if (!var.is_array_size) continue;
    for (const auto* c : hard) {
      if (ConfinedTo(*c, name) && !EvalConstraint(*c)) return false;
    }
  }
  return true;
}

std::unordered_map<std::string, int64_t> ConstraintSolver::DrawArraySizesOnce(
    const std::vector<ConstraintExpr>& extra, bool include_soft,
    const std::function<int64_t(RandVariable&)>& gen) {
  static constexpr int kMaxSizeAttempts = 500;
  std::unordered_map<std::string, int64_t> sizes;
  // With no array size to draw, nothing is drawn here, so that a solve over
  // scalars alone draws the sequence it drew before.
  if (std::none_of(variables_.begin(), variables_.end(),
                   [](const auto& kv) { return kv.second.is_array_size; })) {
    return sizes;
  }
  for (int attempt = 0; attempt < kMaxSizeAttempts; ++attempt) {
    values_.clear();
    real_values_.clear();
    SeedInactiveVariables(variables_, values_, real_values_);
    ApplyDirectConstraints(extra, include_soft);
    DrawArraySizeVariables(variables_, values_, gen);
    if (SizeConstraintsHold(extra)) break;
  }
  for (const auto& [name, var] : variables_) {
    auto it = values_.find(name);
    if (var.is_array_size && it != values_.end()) sizes[name] = it->second;
  }
  return sizes;
}

void ConstraintSolver::HoldArraySizes(
    const std::unordered_map<std::string, int64_t>& sizes) {
  for (const auto& [name, size] : sizes) values_[name] = size;
}

}  // namespace delta
