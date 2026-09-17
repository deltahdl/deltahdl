#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "simulator/constraint_solver.h"
#include "simulator/constraint_solver_internal.h"

namespace delta {

namespace {

// True when the soft constraint directly references 'var' in its own relation
// (the single variable a simple relation names, or any variable recorded in
// ref_vars) or in its inner expression_or_dist. A variable that only gates the
// constraint — for instance the antecedent p of p -> soft q — is not among
// these, so 'disable soft' on such a variable leaves the soft constraint in
// place, as the clause requires.
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
  // 18.5.13.1 / 18.5.13.2: a soft constraint discarded by the priority
  // resolution or by a 'disable soft' directive is not seeded — it must not
  // bias the result toward its preferred value.
  return include_soft && c.kind == ConstraintKind::kSoft &&
         c.inner != nullptr && dropped_soft_.count(&c) == 0 &&
         disabled_soft_.count(&c) == 0;
}

void ConstraintSolver::SeedHonoredSoft(
    const ConstraintExpr& inner, const std::vector<ConstraintExpr>& extra) {
  // 18.5.13: a soft distribution is seeded by sampling it, exactly as a hard
  // dist is; the seeded value is then left untouched by the general draw, so an
  // honored soft dist steers its variable while a discarded one (not seeded at
  // all) leaves it free.
  if (inner.kind == ConstraintKind::kDist) {
    // 18.8: as for a hard dist, sampling a distribution into an inactive
    // variable would replace the state value it is required to hold, so an
    // inactive target is left at its current value.
    if (!HoldsStateValue(inner.var_name)) SeedDist(inner, extra);
    return;
  }
  ApplyConcreteConstraint(inner, values_, rng_,
                          HoldsStateValue(inner.var_name));
}

namespace {

// Narrows the domain `narrowed` holds for the variable of the soft bound
// `inner`, starting from the variable's own domain, by that bound; a
// variable the solver does not hold, an inactive one, a randc one, which is
// drawn from its own cycle, and one already seeded are left alone.
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

// 18.5.13.1: the soft constraints that are bounds on a variable, x > 10 and
// x < 100 held softly, are honored together where they can be: the domain
// each variable is drawn from is narrowed by every honored soft bound on it
// at once, and the variable drawn from that domain ahead of the general
// draw, so that a pair of bounds over an int is met rather than one of them
// being discarded for a draw that met the other alone.
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

// Process one constraint in declaration order for the 'disable soft'
// resolution. A soft constraint is recorded as seen (so a later directive can
// discard it); a 'disable soft' directive discards each already-seen soft
// constraint — exactly the lower-priority ones — that directly references its
// variable.
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

  // Walk the soft constraints and 'disable soft' directives in declaration
  // order (every enabled block, then the inline constraints last) — the order
  // that fixes priority in 18.5.13.1. A directive discards the soft constraints
  // seen before it, which are exactly the ones of lower priority, that directly
  // reference the directive's variable.
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
  // Collect the soft constraints in syntactic declaration order. 18.5.13.1
  // fixes priority by that order: within one construct a constraint declared
  // later has higher priority, and a constraint in an inline (with) block
  // outranks the class constraints. CollectConstraints walks every block in
  // declaration order and then the inline constraints last, so higher-priority
  // constraints come later in 'soft'; iterating from the back therefore visits
  // them highest priority first.
  std::vector<const ConstraintExpr*> hard;
  std::vector<const ConstraintExpr*> soft;
  CollectConstraints(blocks_, extra, hard, soft);

  // Start with every soft constraint discarded, then reinstate them one at a
  // time from highest priority to lowest, retaining each only while the
  // reinstated set stays jointly satisfiable with the hard constraints. A
  // higher-priority constraint that cannot be honored is left discarded but
  // does not block a lower-priority one that can be — this reproduces the
  // clause's conceptual model exactly: for two soft constraints c1 (higher) and
  // c2 (lower) the retained set is {c1,c2} when both hold, else {c1}, else
  // {c2}, else {}.
  dropped_soft_.clear();
  dropped_soft_.insert(soft.begin(), soft.end());
  for (auto it = soft.rbegin(); it != soft.rend(); ++it) {
    // 18.5.13.2: a soft constraint already discarded by a 'disable soft'
    // directive stays discarded — the priority resolution never reinstates it.
    if (disabled_soft_.count(*it)) continue;
    dropped_soft_.erase(*it);  // tentatively reinstate this constraint
    if (!SolveIterative(extra, /*include_soft=*/true)) {
      // A hard-constraint guard error is unaffected by discarding soft
      // constraints, so it fails the call outright rather than being retried.
      if (guard_error_) return false;
      dropped_soft_.insert(*it);  // not satisfiable together: discard it again
    }
  }

  // Commit a final solution honoring exactly the retained soft set. Each
  // retention step above kept the set satisfiable, so the retained set has a
  // solution; the call fails only if the hard constraints alone are
  // unsatisfiable. When the soft set involves only soft constraints this can
  // never fail — the empty retained set is always solvable — which is the
  // property the clause guarantees for a randomize() call over soft
  // constraints only.
  return SolveIterative(extra, /*include_soft=*/true);
}

}  // namespace delta
