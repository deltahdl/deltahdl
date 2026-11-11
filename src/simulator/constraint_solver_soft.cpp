#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "simulator/constraint_solver.h"
#include "simulator/constraint_solver_internal.h"

namespace delta {

namespace {

bool SoftDirectlyReferences(const ConstraintExpr& soft,
                            const std::string& var) {
  if (soft.var_name == var) return true;
  for (const auto& r : soft.ref_vars)
    if (r == var) return true;
  if (soft.inner) {
    if (soft.inner->var_name == var) return true;
    for (const auto& r : soft.inner->ref_vars)
      if (r == var) return true;
  }
  return false;
}

}  // namespace

bool ConstraintSolver::SoftSeedApplies(const ConstraintExpr& c,
                                       bool include_soft) const {
  return include_soft && c.kind == ConstraintKind::kSoft &&
         c.inner != nullptr && dropped_soft_.count(&c) == 0 &&
         disabled_soft_.count(&c) == 0;
}

void ConstraintSolver::SeedHonoredSoft(
    const ConstraintExpr& inner, const std::vector<ConstraintExpr>& extra) {
  if (inner.kind == ConstraintKind::kDist) {
    if (!HoldsStateValue(inner.var_name)) SeedDist(inner, extra);
    return;
  }
  ApplyConcreteConstraint(inner, values_, rng_,
                          HoldsStateValue(inner.var_name));
}

namespace {

void NarrowBySoftBound(
    const ConstraintExpr& inner,
    const std::unordered_map<std::string, RandVariable>& variables,
    const std::unordered_map<std::string, int64_t>& values,
    std::unordered_map<std::string, RandVariable>& narrowed) {
  if (!IsComparison(inner.kind)) return;
  auto it = variables.find(inner.var_name);
  if (it == variables.end() || !it->second.enabled ||
      it->second.qualifier == RandQualifier::kRandc ||
      values.count(inner.var_name) != 0) {
    return;
  }
  RandVariable& dom =
      narrowed.try_emplace(inner.var_name, it->second).first->second;
  dom = Narrowed(dom, inner);
}

}  // namespace

void ConstraintSolver::SeedSoftBounds(const std::vector<ConstraintExpr>& extra,
                                      bool include_soft) {
  std::unordered_map<std::string, RandVariable> narrowed;
  auto fold = [&](const ConstraintExpr& c) {
    if (SoftSeedApplies(c, include_soft))
      NarrowBySoftBound(*c.inner, variables_, values_, narrowed);
  };
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) fold(c);
  }
  for (const auto& c : extra) fold(c);
  for (auto& [name, dom] : narrowed) {
    if (dom.min_val > dom.max_val) continue;
    values_[name] = GenerateRandValue(dom);
  }
}

namespace {

void VisitDisableSoftConstraint(
    const ConstraintExpr& c, std::vector<const ConstraintExpr*>& seen_soft,
    std::unordered_set<const ConstraintExpr*>& disabled_soft) {
  if (c.kind == ConstraintKind::kSoft) {
    seen_soft.push_back(&c);
  } else if (c.kind == ConstraintKind::kDisableSoft) {
    for (const auto* s : seen_soft) {
      if (SoftDirectlyReferences(*s, c.var_name)) disabled_soft.insert(s);
    }
  }
}

}  // namespace

void ConstraintSolver::ComputeDisabledSoft(
    const std::vector<ConstraintExpr>& extra) {
  disabled_soft_.clear();

  std::vector<const ConstraintExpr*> seen_soft;
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      VisitDisableSoftConstraint(c, seen_soft, disabled_soft_);
    }
  }
  for (const auto& c : extra) {
    VisitDisableSoftConstraint(c, seen_soft, disabled_soft_);
  }
}

bool ConstraintSolver::SolveBySoftPriority(
    const std::vector<ConstraintExpr>& extra) {
  std::vector<const ConstraintExpr*> hard;
  std::vector<const ConstraintExpr*> soft;
  CollectConstraints(blocks_, extra, hard, soft);

  dropped_soft_.clear();
  dropped_soft_.insert(soft.begin(), soft.end());
  for (auto it = soft.rbegin(); it != soft.rend(); ++it) {
    if (disabled_soft_.count(*it)) continue;
    dropped_soft_.erase(*it);
    if (HonoredBoundsConflict(extra) || !SolveIterative(extra, true)) {
      if (guard_error_) return false;
      dropped_soft_.insert(*it);
    }
  }

  return SolveIterative(extra, true);
}

}  // namespace delta
