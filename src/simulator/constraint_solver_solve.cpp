#include <algorithm>
#include <cstdint>
#include <functional>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "simulator/constraint_solver.h"
#include "simulator/constraint_solver_internal.h"

namespace delta {

namespace {

// depth(v) = the longest chain of variables that must be solved after v in the
// solve...before successor graph. Variables with nothing ordered after them
// have depth 0; a variable solved before others has a strictly greater depth
// than each of them. Memoizes into 'depth' and guards self-referential cycles
// (the elaborator rejects real cycles) with the on-stack set.
int SolveGroupDepth(
    const std::string& v,
    const std::unordered_map<std::string, std::vector<std::string>>& succ,
    std::unordered_map<std::string, int>& depth,
    std::unordered_set<std::string>& on_stack) {
  auto cached = depth.find(v);
  if (cached != depth.end()) return cached->second;
  if (on_stack.count(v)) return 0;  // cycle guard (elaborator rejects cycles)
  on_stack.insert(v);
  int best = 0;
  auto it = succ.find(v);
  if (it != succ.end()) {
    for (const auto& w : it->second) {
      best = std::max(best, 1 + SolveGroupDepth(w, succ, depth, on_stack));
    }
  }
  on_stack.erase(v);
  depth[v] = best;
  return best;
}

// Depth-first walk of the function-argument priority digraph (higher -> lower)
// that sets 'cycle' true on encountering a gray (on-stack) successor — a back
// edge that closes a cycle. 'color': 0 white, 1 gray, 2 black.
void PriorityCycleDfs(
    const std::string& v,
    const std::unordered_map<std::string, std::vector<std::string>>& succ,
    std::unordered_map<std::string, int>& color, bool& cycle) {
  color[v] = 1;
  auto it = succ.find(v);
  if (it != succ.end()) {
    for (const auto& w : it->second) {
      if (color[w] == 1) {
        cycle = true;
        return;
      }
      if (color[w] == 0) {
        PriorityCycleDfs(w, succ, color, cycle);
        if (cycle) return;
      }
    }
  }
  color[v] = 2;
}

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

// One relaxation sweep over every priority edge: a successor's rank is pushed
// to at least one past its predecessor's. Returns true when some rank changed,
// so the caller can stop once the ranks reach their fixpoint.
bool RelaxPriorityRanks(
    const std::unordered_map<std::string, std::vector<std::string>>& succ,
    std::unordered_map<std::string, int>& prank) {
  bool changed = false;
  for (const auto& [h, ls] : succ) {
    for (const auto& l : ls) {
      if (prank[l] < prank[h] + 1) {
        prank[l] = prank[h] + 1;
        changed = true;
      }
    }
  }
  return changed;
}

// prank(v) = how many variables must be solved before v, i.e. its distance from
// a source of the priority digraph (higher -> lower successor edges). A
// variable with nothing ordered before it has rank 0; each successor sits at
// least one rank past every predecessor. Computed by iteratively relaxing along
// the edges from the sources; the graph is acyclic here, so |vars| passes
// suffice to reach the fixpoint.
std::unordered_map<std::string, int> ComputePriorityRanks(
    const std::vector<std::string>& vars,
    const std::unordered_map<std::string, std::vector<std::string>>& succ) {
  std::unordered_map<std::string, int> prank;
  for (const auto& v : vars) prank[v] = 0;
  for (size_t pass = 0; pass < vars.size(); ++pass) {
    if (!RelaxPriorityRanks(succ, prank)) break;
  }
  return prank;
}

// 18.8 / 18.5.8: an inactive variable (rand_mode() OFF) is not one of the
// active random variables, so it is not randomized. The solver instead seeds
// its current value as a constant before solving (the real value into
// 'real_values', the integral value into 'values') so a global constraint
// relating it to an active variable is evaluated against that fixed value
// rather than dropped.
void SeedInactiveVariables(
    std::unordered_map<std::string, RandVariable>& variables,
    std::unordered_map<std::string, int64_t>& values,
    std::unordered_map<std::string, double>& real_values) {
  for (auto& [name, var] : variables) {
    // 18.4.1: a real variable's value lives in real_values, not the integral
    // values map; an inactive one likewise holds its current real value.
    if (var.is_real) {
      if (!var.enabled) real_values[name] = var.real_value;
      continue;
    }
    if (!var.enabled) values[name] = var.value;
  }
}

// 18.4.2: the cyclic (randc) variables shall be solved before the noncyclical
// rand variables. Draw every still-uncommitted active randc value here so the
// rand variables that follow are solved with the cyclic values already fixed
// for this attempt.
void DrawRandcVariables(
    std::unordered_map<std::string, RandVariable>& variables,
    std::unordered_map<std::string, int64_t>& values,
    const std::function<int64_t(RandVariable&)>& gen) {
  for (auto& [name, var] : variables) {
    if (!var.enabled || var.is_real) continue;
    if (var.qualifier != RandQualifier::kRandc) continue;
    if (values.find(name) != values.end()) continue;
    values[name] = gen(var);
  }
}

// 18.5.7.1: an array's size method is solved with the size constraints, ahead
// of the iterative (foreach) constraints over that array. Commit every active,
// non-randc, still-uncommitted array-size variable here so a foreach reading
// the size sees the chosen value and treats it as a state variable.
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

// The default single (flat) general pass: draw every active variable not
// already committed. 18.4.1 draws an active real variable from its uniform real
// range; the already-committed randc/array-size integral variables are skipped.
void DrawGeneralPass(std::unordered_map<std::string, RandVariable>& variables,
                     std::unordered_map<std::string, int64_t>& values,
                     std::unordered_map<std::string, double>& real_values,
                     const std::function<int64_t(RandVariable&)>& gen,
                     const std::function<double(RandVariable&)>& gen_real) {
  for (auto& [name, var] : variables) {
    if (!var.enabled) continue;
    if (var.is_real) {
      real_values[name] = gen_real(var);
      continue;
    }
    if (values.find(name) != values.end()) continue;
    values[name] = gen(var);
  }
}

// A constraint is checkable in a partial assignment only once every variable it
// references has been committed. A constraint that references nothing is
// deferred to the final pass (treated as not ready here).
bool ConstraintReady(const ConstraintExpr& c,
                     const std::unordered_set<std::string>& committed) {
  if (c.ref_vars.empty()) return false;  // checked only in the final pass
  for (const auto& v : c.ref_vars) {
    if (!committed.count(v)) return false;
  }
  return true;
}

// Seed a single concrete constraint directly into 'values': an equality fixes
// the variable to its constant, and a set-membership picks one of the listed
// values at random. Other kinds leave 'values' untouched.
void ApplyConcreteConstraint(const ConstraintExpr& c,
                             std::unordered_map<std::string, int64_t>& values,
                             std::mt19937& rng) {
  if (c.kind == ConstraintKind::kEqual) {
    values[c.var_name] = c.lo;
  } else if (c.kind == ConstraintKind::kSetMembership) {
    if (!c.set_values.empty()) {
      std::uniform_int_distribution<size_t> pick(0, c.set_values.size() - 1);
      values[c.var_name] = c.set_values[pick(rng)];
    }
  }
}

}  // namespace

bool ConstraintSolver::Solve() { return SolveWith({}); }

bool ConstraintSolver::Check(const std::vector<ConstraintExpr>& constraints) {
  // 18.12: the no-argument scope randomize is a pure checker. Unlike SolveWith,
  // it never generates a new value for any variable: each variable's current
  // value is taken as is, and the constraints are only evaluated against those
  // values. Every constraint expression is evaluated and the call fails the
  // moment one of them is false, succeeding only when every one holds.
  guard_error_ = false;
  // 18.5.10: a static block's shared on/off state may have been changed through
  // another instance; reflect it before evaluating the constraints.
  RefreshStaticBlockState();
  for (const auto& [name, var] : variables_) {
    values_[name] = var.value;
  }
  return CheckAllConstraints(constraints, /*include_soft=*/true);
}

bool ConstraintSolver::InlineConstraintCheck(
    const std::vector<ConstraintExpr>& constraints) {
  // 18.11.1: the null argument empties the active random set. Force every
  // variable into state-variable status — regardless of its declared rand or
  // randc qualifier or its current rand_mode — so the solver randomizes none of
  // them for this call.
  for (auto& entry : variables_) {
    entry.second.enabled = false;
  }
  // With nothing left to randomize, the call is a pure checker: it takes each
  // member's current value as is and only evaluates whether the constraints are
  // satisfied, returning 1 when they all hold and 0 otherwise. The checker
  // mechanics are exactly those of the no-argument checker, so defer to it.
  return Check(constraints);
}

void ConstraintSolver::ApplyDirectConstraints(
    const std::vector<ConstraintExpr>& extra, bool include_soft) {
  auto apply = [this](const ConstraintExpr& c) {
    ApplyConcreteConstraint(c, values_, rng_);
  };
  // 18.5.13: when the soft constraints are still active, seed their inner
  // expression_or_dist exactly as a hard constraint so a satisfiable soft
  // preference is honored. A hard constraint applied afterward takes precedence
  // and overwrites any conflicting soft seed, leaving the conflicting soft to
  // be discarded by the include_soft-clear retry.
  auto seed = [&](const ConstraintExpr& c) {
    // 18.5.13.1 / 18.5.13.2: a soft constraint discarded by the priority
    // resolution or by a 'disable soft' directive is not seeded — it must not
    // bias the result toward its preferred value.
    if (include_soft && c.kind == ConstraintKind::kSoft && c.inner &&
        !dropped_soft_.count(&c) && !disabled_soft_.count(&c)) {
      apply(*c.inner);
    } else {
      apply(c);
    }
  };
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) seed(c);
  }
  for (const auto& c : extra) seed(c);
}

bool ConstraintSolver::SolveWith(
    const std::vector<ConstraintExpr>& inline_constraints) {
  // 18.5.10: pick up any constraint_mode() change made through another instance
  // of the class via a shared static block before deciding which blocks apply.
  RefreshStaticBlockState();

  // 18.5.3: a dist operation shall not be applied to a randc variable, and a
  // dist expression requires at least one rand variable. A distribution that
  // violates either limitation makes randomization fail outright.
  if (HasDistOnRandc()) return false;
  if (DistLacksRandVariable()) return false;

  // 18.5.4: a uniqueness constraint group may not contain a randc variable and
  // all of its members shall be of equivalent type. An illegal group makes
  // randomization fail outright.
  if (HasRandcInUnique()) return false;
  if (UniqueMembersNotEquivalentType()) return false;

  // 18.5.11: a circular dependency among the implicit priorities created by
  // using random variables as function arguments is an error; randomize() fails
  // outright rather than attempting to solve a self-contradictory ordering.
  if (HasFunctionArgPriorityCycle()) return false;

  if (pre_randomize_) pre_randomize_();

  // 18.6.3: if randomize() fails, the random variables retain their previous
  // values. The iterative solver overwrites the solved-value maps in place as
  // it searches, so capture them here and restore them should the solve fail,
  // so a failed randomize() leaves the variables exactly as the caller last saw
  // them.
  const std::unordered_map<std::string, int64_t> kPrevValues = values_;
  const std::unordered_map<std::string, double> kPrevRealValues = real_values_;

  // 18.5.13.2: resolve the 'disable soft' directives before solving. Each
  // discards the lower-priority soft constraints that directly reference its
  // variable; those stay discarded for the whole call, independent of and ahead
  // of the priority resolution among the soft constraints that remain.
  ComputeDisabledSoft(inline_constraints);

  // 18.5.13: hard constraints shall always be satisfied or randomization fails.
  // First try to satisfy them together with the full soft set. With no soft
  // constraint discarded this is the original 18.5.13 path, kept intact for the
  // common case where every soft constraint can be honored.
  dropped_soft_.clear();
  bool solved = SolveIterative(inline_constraints, /*include_soft=*/true);

  // 18.5.13.1: when the full soft set has no joint solution, the soft
  // constraints are not all dropped at once; they are discarded by priority so
  // the highest-priority preferences still hold. A guard ERROR, by contrast,
  // fails randomize() outright regardless of any soft constraint.
  if (!solved && !guard_error_) {
    solved = SolveBySoftPriority(inline_constraints);
  }

  // The discarded-soft set is meaningful only while resolving this call's
  // priorities; clear it so it never carries into a later checker evaluation,
  // which would otherwise skip the soft constraints it lists.
  dropped_soft_.clear();
  // 18.5.13.2: likewise scoped to this call; clear it so a 'disable soft'
  // directive never carries into a later solve or checker evaluation.
  disabled_soft_.clear();

  if (solved) {
    // 18.6.3: a static random variable is shared by every instance; publish the
    // values just drawn so the other instances observe the change.
    CommitStaticSharedValues();
  } else {
    // 18.6.3: the solve failed, so restore the values the variables held before
    // this call rather than leaving the solver's partial search state behind.
    values_ = kPrevValues;
    real_values_ = kPrevRealValues;
  }

  // 18.6.3: post_randomize() is not called when randomize() fails.
  if (solved && post_randomize_) post_randomize_();
  return solved;
}

void ConstraintSolver::CommitStaticSharedValues() {
  for (auto& [name, var] : variables_) {
    if (!var.is_static || !var.shared_value) continue;
    auto it = values_.find(name);
    if (it != values_.end()) *var.shared_value = it->second;
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

void ConstraintSolver::ApplyDistConstraints() {
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (c.kind == ConstraintKind::kDist) {
        values_[c.var_name] = SampleDist(c);
      }
    }
  }
}

std::vector<std::vector<std::string>> ConstraintSolver::ComputeSolveGroups(
    const std::vector<std::string>& vars) const {
  std::unordered_set<std::string> var_set(vars.begin(), vars.end());
  // before -> {afters}, restricted to the variables being solved in this pass.
  std::unordered_map<std::string, std::vector<std::string>> succ;
  for (const auto& [b, a] : solve_before_edges_) {
    if (var_set.count(b) && var_set.count(a)) succ[b].push_back(a);
  }
  // depth(v) = the longest chain of variables that must be solved after v.
  // Variables with nothing ordered after them have depth 0; a variable solved
  // before others has a strictly greater depth than each of them. Solving in
  // descending depth therefore honors every ordering edge while deferring each
  // variable as late as the ordering allows.
  std::unordered_map<std::string, int> depth;
  int max_depth = 0;
  for (const auto& v : vars) {
    std::unordered_set<std::string> on_stack;
    max_depth = std::max(max_depth, SolveGroupDepth(v, succ, depth, on_stack));
  }
  // Bucket by depth, highest depth (solved first) into the earliest group; the
  // unordered variables sit at depth 0 and so form the final, last-solved
  // group.
  std::vector<std::vector<std::string>> buckets(max_depth + 1);
  for (const auto& v : vars) buckets[max_depth - depth[v]].push_back(v);
  std::vector<std::vector<std::string>> groups;
  for (auto& g : buckets) {
    if (!g.empty()) groups.push_back(std::move(g));
  }
  return groups;
}

bool ConstraintSolver::SolveOrderedGroups(
    const std::vector<std::vector<std::string>>& groups, size_t idx,
    const std::vector<ConstraintExpr>& extra, bool include_soft) {
  // Every group committed: the assignment is complete, so accept it only if all
  // constraints hold against the fully populated value set.
  if (idx == groups.size()) return CheckAllConstraints(extra, include_soft);
  static constexpr int kGroupAttempts = 200;
  for (int attempt = 0; attempt < kGroupAttempts; ++attempt) {
    for (const auto& name : groups[idx]) {
      auto it = variables_.find(name);
      if (it == variables_.end()) continue;
      values_[name] = GenerateRandValue(it->second);
    }
    // Hold this group's draw fixed and try to complete the remaining groups.
    if (SolveOrderedGroups(groups, idx + 1, extra, include_soft)) return true;
    // 18.5.12: an ERROR guard fails randomize() outright; do not keep retrying.
    if (guard_error_) return false;
  }
  return false;
}

bool ConstraintSolver::HasFunctionArgPriorityCycle() const {
  // Build the priority digraph (higher -> lower) and look for a back edge with
  // a depth-first walk. A gray (on-stack) successor closes a cycle, e.g. one
  // variable used as a function argument in a constraint on a second while the
  // second is used as a function argument in a constraint on the first.
  std::unordered_map<std::string, std::vector<std::string>> succ;
  std::unordered_set<std::string> nodes;
  for (const auto& [h, l] : function_arg_priority_edges_) {
    succ[h].push_back(l);
    nodes.insert(h);
    nodes.insert(l);
  }
  std::unordered_map<std::string, int> color;  // 0 white, 1 gray, 2 black
  bool cycle = false;
  for (const auto& v : nodes) {
    if (color[v] == 0) {
      PriorityCycleDfs(v, succ, color, cycle);
      if (cycle) break;
    }
  }
  return cycle;
}

std::vector<std::vector<std::string>> ConstraintSolver::ComputePriorityLayers(
    const std::vector<std::string>& vars) const {
  std::unordered_set<std::string> var_set(vars.begin(), vars.end());
  // pred -> {successors}, i.e. higher -> lower, restricted to vars in this
  // pass.
  std::unordered_map<std::string, std::vector<std::string>> succ;
  for (const auto& [h, l] : function_arg_priority_edges_) {
    if (var_set.count(h) && var_set.count(l)) succ[h].push_back(l);
  }
  // prank(v) = how many variables must be solved before v, i.e. its distance
  // from a source of the priority digraph. A variable with nothing ordered
  // before it has rank 0 and is solved in the first (highest-priority) layer;
  // each successor sits at least one rank past every predecessor. Solving in
  // ascending rank therefore honors every priority edge and gathers the
  // unordered variables into layer 0. The rank is computed by relaxing along
  // the edges from the sources.
  std::unordered_map<std::string, int> prank = ComputePriorityRanks(vars, succ);
  int max_rank = 0;
  for (const auto& v : vars) max_rank = std::max(max_rank, prank[v]);
  std::vector<std::vector<std::string>> layers(max_rank + 1);
  for (const auto& v : vars) layers[prank[v]].push_back(v);
  std::vector<std::vector<std::string>> out;
  for (auto& g : layers) {
    if (!g.empty()) out.push_back(std::move(g));
  }
  return out;
}

namespace {

// Every hard constraint that has become checkable under 'committed' must hold;
// constraints whose referenced variables are not all committed yet are skipped
// (they are evaluated once more variables are fixed). 'eval' evaluates one
// constraint against the current value set.
bool AllCommittedHardConstraintsHold(
    const std::vector<const ConstraintExpr*>& hard,
    const std::unordered_set<std::string>& committed,
    const std::function<bool(const ConstraintExpr&)>& eval) {
  for (const auto* c : hard) {
    if (!ConstraintReady(*c, committed)) continue;
    if (!eval(*c)) return false;
  }
  return true;
}

// Each checkable soft constraint's inner expression_or_dist must hold under
// 'committed'; not-yet-checkable ones are skipped, as for hard constraints.
bool AllCommittedSoftConstraintsHold(
    const std::vector<const ConstraintExpr*>& soft,
    const std::unordered_set<std::string>& committed,
    const std::function<bool(const ConstraintExpr&)>& eval) {
  for (const auto* c : soft) {
    if (!ConstraintReady(*c, committed)) continue;
    const ConstraintExpr* inner = c->inner ? c->inner : nullptr;
    if (inner && !eval(*inner)) return false;
  }
  return true;
}

}  // namespace

bool ConstraintSolver::CheckCommittedConstraints(
    const std::vector<ConstraintExpr>& extra, bool include_soft,
    const std::unordered_set<std::string>& committed) const {
  std::vector<const ConstraintExpr*> hard;
  std::vector<const ConstraintExpr*> soft;
  CollectConstraints(blocks_, extra, hard, soft);
  auto eval = [this](const ConstraintExpr& c) { return EvalConstraint(c); };
  if (!AllCommittedHardConstraintsHold(hard, committed, eval)) return false;
  if (include_soft && !AllCommittedSoftConstraintsHold(soft, committed, eval)) {
    return false;
  }
  return true;
}

namespace {

// committed starts from every variable already fixed before the general pass —
// the inactive (state) variables, the randc draws, the array sizes, and the
// real variables — all of which are present in values_/real_values_ by now.
std::unordered_set<std::string> CommittedFromValues(
    const std::unordered_map<std::string, int64_t>& values,
    const std::unordered_map<std::string, double>& real_values) {
  std::unordered_set<std::string> committed;
  for (const auto& kv : values) committed.insert(kv.first);
  for (const auto& kv : real_values) committed.insert(kv.first);
  return committed;
}

// Draw one priority layer up to 'attempts' times, returning true as soon as a
// draw leaves the now-checkable constraints satisfied against 'committed' plus
// this layer. 'draw_layer' redraws every variable in the layer; 'check' tests
// the constraints against a committed set.
bool DrawAndCheckPriorityLayer(
    const std::vector<std::string>& layer,
    const std::unordered_set<std::string>& committed, int attempts,
    const std::function<void(const std::vector<std::string>&)>& draw_layer,
    const std::function<bool(const std::unordered_set<std::string>&)>& check) {
  for (int attempt = 0; attempt < attempts; ++attempt) {
    draw_layer(layer);
    std::unordered_set<std::string> with_layer = committed;
    for (const auto& name : layer) with_layer.insert(name);
    if (check(with_layer)) return true;
  }
  return false;
}

}  // namespace

bool ConstraintSolver::SolvePriorityLayers(
    const std::vector<std::vector<std::string>>& layers,
    const std::vector<ConstraintExpr>& extra, bool include_soft) {
  static constexpr int kLayerAttempts = 200;
  std::unordered_set<std::string> committed =
      CommittedFromValues(values_, real_values_);
  auto draw_layer = [this](const std::vector<std::string>& layer) {
    for (const auto& name : layer) {
      auto it = variables_.find(name);
      if (it == variables_.end()) continue;
      values_[name] = GenerateRandValue(it->second);
    }
  };
  auto check = [&](const std::unordered_set<std::string>& with_layer) {
    return CheckCommittedConstraints(extra, include_soft, with_layer);
  };
  for (const auto& layer : layers) {
    // 18.5.11: an earlier, higher-priority layer is never reconsidered. If no
    // draw of this layer satisfies the constraints that have become checkable,
    // the overall solve fails — the subdivision can make the set unsolvable.
    if (!DrawAndCheckPriorityLayer(layer, committed, kLayerAttempts, draw_layer,
                                   check)) {
      return false;
    }
    for (const auto& name : layer) committed.insert(name);
  }
  // Every layer committed: accept only if the complete assignment satisfies all
  // constraints, including any whose referenced variables were left unlisted.
  return CheckAllConstraints(extra, include_soft);
}

// Staged solve shared by the function-argument priority pass (18.5.11) and the
// solve...before ordered pass (18.5.9). Both passes commit the active real
// variables first, gather the still-uncommitted active integral variables into
// 'general', partition that set, and run the staged integral solve over the
// partition. The only differences are the partition and staged-solve routines,
// injected as callbacks, and which clause's wording applies (use_priority); the
// surrounding token sequence is identical, so it is unified here.
//
// Returns true when the staged solve succeeds (the caller should return true),
// false otherwise. The caller still checks guard_error_ to decide whether the
// outer attempt loop continues or aborts, exactly as before.
// Real variables are committed first (as in the flat pass), so any ordered
// integral group/layer is completed against them.
static void CommitStagedRealVariables(
    std::unordered_map<std::string, RandVariable>& variables,
    std::unordered_map<std::string, double>& real_values,
    const std::function<double(RandVariable&)>& gen_real) {
  for (auto& [name, var] : variables) {
    if (var.enabled && var.is_real) {
      real_values[name] = gen_real(var);
    }
  }
}

// Gather the still-uncommitted active integral variables — the set the staged
// pass partitions and solves. randc, array-size, and inactive variables are
// already committed; the cyclical ones in particular are solved first, as the
// clause requires.
static std::vector<std::string> CollectStagedGeneralVariables(
    const std::unordered_map<std::string, RandVariable>& variables,
    const std::unordered_map<std::string, int64_t>& values) {
  std::vector<std::string> general;
  for (const auto& [name, var] : variables) {
    if (!var.enabled || var.is_real) continue;
    if (values.find(name) != values.end()) continue;
    general.push_back(name);
  }
  return general;
}

// The solver's mutable random-variable value store, the one domain object a
// staged pass works over: the rand variables (18.4) plus the two value maps
// that hold their solved values — the integral values and, separately for real
// (18.4.1) variables, the real values. Bundled so a staged pass takes the store
// as one entity rather than its three constituent maps spread apart.
struct StagedSolveState {
  std::unordered_map<std::string, RandVariable>& variables;
  std::unordered_map<std::string, double>& real_values;
  const std::unordered_map<std::string, int64_t>& values;
};

static bool RunStagedSolve(
    StagedSolveState state, bool use_priority,
    const std::function<double(RandVariable&)>& gen_real,
    const std::function<std::vector<std::vector<std::string>>(
        const std::vector<std::string>&)>& partition,
    const std::function<bool(const std::vector<std::vector<std::string>>&)>&
        solve) {
  (void)use_priority;
  CommitStagedRealVariables(state.variables, state.real_values, gen_real);
  std::vector<std::string> general =
      CollectStagedGeneralVariables(state.variables, state.values);
  return solve(partition(general));
}

namespace {

// The outcome of one staged or flat attempt within SolveIterative's retry loop.
enum class AttemptOutcome : std::uint8_t {
  kSolved,  // a complete satisfying assignment was found; return true
  kAbort,   // a guard ERROR was hit; randomize() fails outright (return false)
  kRetry,   // no solution this attempt; the loop should try again
};

// Collapse the shared "solved? / guard error? / retry" decision used after a
// pass runs. 'pass' runs the staged or flat solve (and may set the guard flag);
// 'guard_error' is read afterward to distinguish an outright failure from an
// ordinary retry.
AttemptOutcome ResolveAttempt(const std::function<bool()>& pass,
                              const bool& guard_error) {
  if (pass()) return AttemptOutcome::kSolved;
  if (guard_error) return AttemptOutcome::kAbort;
  return AttemptOutcome::kRetry;
}

// The three mutually-exclusive solve strategies one attempt may run, the entity
// SolveIterative chooses among: the priority-layer staged pass (18.5.11), the
// solve...before ordered staged pass (18.5.9), and the default flat pass.
// Exactly one is invoked per attempt, selected by which ordering edges exist.
struct AttemptPasses {
  const std::function<bool()>& priority;
  const std::function<bool()>& ordered;
  const std::function<bool()>& flat;
};

// Select and run the one pass that applies for this attempt — the
// priority-layer staged pass (18.5.11), the solve...before ordered staged pass
// (18.5.9), or the default flat pass — and resolve its outcome. Exactly one of
// the passes runs, chosen by which ordering edges exist, just as the original
// inline branch chain did.
AttemptOutcome RunAttemptPass(bool has_priority_edges, bool has_before_edges,
                              const AttemptPasses& passes,
                              const bool& guard_error) {
  if (has_priority_edges) return ResolveAttempt(passes.priority, guard_error);
  if (has_before_edges) return ResolveAttempt(passes.ordered, guard_error);
  return ResolveAttempt(passes.flat, guard_error);
}

}  // namespace

bool ConstraintSolver::SolveIterative(const std::vector<ConstraintExpr>& extra,
                                      bool include_soft) {
  static constexpr int kMaxAttempts = 500;
  guard_error_ = false;
  auto gen = [this](RandVariable& var) { return GenerateRandValue(var); };
  auto gen_real = [this](RandVariable& var) {
    return GenerateRandRealValue(var);
  };
  // 18.5.11: when random variables are used as function arguments, the implied
  // priority is solved in layers — the higher-priority variables first, each
  // layer committed as state variables to the next without backtracking. This
  // subdivides the solution space (and can fail), distinct from the
  // solution-space-preserving solve...before ordering.
  StagedSolveState state{variables_, real_values_, values_};
  auto priority_pass = [&] {
    return RunStagedSolve(
        state, /*use_priority=*/true, gen_real,
        [this](const std::vector<std::string>& general) {
          return ComputePriorityLayers(general);
        },
        [&](const std::vector<std::vector<std::string>>& layers) {
          return SolvePriorityLayers(layers, extra, include_soft);
        });
  };
  // 18.5.9: a solve...before ordering solves the active integral rand variables
  // in ordered groups; an earlier group is committed before the later groups
  // are solved against it, shifting the probability distribution to match the
  // ordering while leaving the set of legal solutions unchanged.
  auto ordered_pass = [&] {
    return RunStagedSolve(
        state, /*use_priority=*/false, gen_real,
        [this](const std::vector<std::string>& general) {
          return ComputeSolveGroups(general);
        },
        [&](const std::vector<std::vector<std::string>>& groups) {
          return SolveOrderedGroups(groups, 0, extra, include_soft);
        });
  };
  // With no ordering the default single pass is used unchanged; it already
  // draws each legal value combination with uniform probability.
  auto flat_pass = [&] {
    DrawGeneralPass(variables_, values_, real_values_, gen, gen_real);
    return CheckAllConstraints(extra, include_soft);
  };
  for (int attempt = 0; attempt < kMaxAttempts; ++attempt) {
    values_.clear();
    real_values_.clear();
    SeedInactiveVariables(variables_, values_, real_values_);
    ApplyDistConstraints();
    ApplyDirectConstraints(extra, include_soft);
    DrawRandcVariables(variables_, values_, gen);
    DrawArraySizeVariables(variables_, values_, gen);
    AttemptPasses passes{priority_pass, ordered_pass, flat_pass};
    AttemptOutcome outcome =
        RunAttemptPass(!function_arg_priority_edges_.empty(),
                       !solve_before_edges_.empty(), passes, guard_error_);
    if (outcome == AttemptOutcome::kSolved) return true;
    // 18.5.12: an ERROR guard fails randomize() outright; do not retry it.
    if (outcome == AttemptOutcome::kAbort) return false;
  }
  return false;
}

int64_t ConstraintSolver::GetValue(std::string_view name) const {
  // 18.6.3: a static random variable is shared by all instances of its class,
  // so its committed value lives in the shared cell. Read it there when one is
  // attached, so this instance observes the value another instance most
  // recently drew rather than only the value this instance itself last solved.
  auto vit = variables_.find(std::string(name));
  if (vit != variables_.end() && vit->second.is_static &&
      vit->second.shared_value) {
    return *vit->second.shared_value;
  }
  auto it = values_.find(std::string(name));
  return (it != values_.end()) ? it->second : 0;
}

double ConstraintSolver::GetRealValue(std::string_view name) const {
  auto it = real_values_.find(std::string(name));
  return (it != real_values_.end()) ? it->second : 0.0;
}

}  // namespace delta
