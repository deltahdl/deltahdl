#include <algorithm>
#include <cstdint>
#include <functional>
#include <iterator>
#include <string>
#include <unordered_map>
#include <vector>

#include "simulator/constraint_solver.h"

namespace delta {

// 18.4.2: a randc variable takes the next value of its permutation once per
// randomize(), whatever the attempts the other variables take, so the value
// is drawn once into `drawn` and answered from there across them.
std::function<int64_t(RandVariable&)> ConstraintSolver::RandcOncePerSolve(
    std::unordered_map<std::string, int64_t>& drawn) {
  return [this, &drawn](RandVariable& var) {
    auto it = drawn.find(var.name);
    if (it != drawn.end()) return it->second;
    int64_t v = GenerateRandValue(var);
    drawn[var.name] = v;
    return v;
  };
}

// 18.4.2: after an attempt found no solution, a randc value one of the
// constraints naming it refuses is passed over for the next of its
// permutation, and one every such constraint admits is kept.
void ConstraintSolver::PruneRefusedRandcValues(
    std::unordered_map<std::string, int64_t>& drawn,
    const std::vector<ConstraintExpr>& extra) const {
  for (auto it = drawn.begin(); it != drawn.end();) {
    it = RandcValueAdmissible(it->first, extra) ? std::next(it)
                                                : drawn.erase(it);
  }
}

// Whether the constraint `c` names the variable `name`, as the variable it
// constrains, among the ones it references, or in a constraint it guards.
static bool ConstraintNames(const ConstraintExpr& c, const std::string& name) {
  if (c.var_name == name) return true;
  if (std::find(c.ref_vars.begin(), c.ref_vars.end(), name) !=
      c.ref_vars.end()) {
    return true;
  }
  for (const auto& sub : c.sub_constraints) {
    if (ConstraintNames(sub, name)) return true;
  }
  for (const auto& sub : c.else_constraints) {
    if (ConstraintNames(sub, name)) return true;
  }
  return false;
}

bool ConstraintSolver::RandcValueAdmissible(
    const std::string& name, const std::vector<ConstraintExpr>& extra) const {
  auto refuses = [&](const ConstraintExpr& c) {
    return ConstraintNames(c, name) && !EvalConstraint(c);
  };
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (refuses(c)) return false;
    }
  }
  for (const auto& c : extra) {
    if (refuses(c)) return false;
  }
  return true;
}

}  // namespace delta
