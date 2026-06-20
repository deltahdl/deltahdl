#include <algorithm>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "simulator/constraint_solver.h"
#include "simulator/constraint_solver_internal.h"

namespace delta {

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
    if (c.kind == ConstraintKind::kEqual) {
      values_[c.var_name] = c.lo;
    } else if (c.kind == ConstraintKind::kSetMembership) {
      if (!c.set_values.empty()) {
        std::uniform_int_distribution<size_t> pick(0, c.set_values.size() - 1);
        values_[c.var_name] = c.set_values[pick(rng_)];
      }
    }
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

void ConstraintSolver::ComputeDisabledSoft(
    const std::vector<ConstraintExpr>& extra) {
  disabled_soft_.clear();

  // The variables that directly appear in a soft constraint's relation: the
  // single variable a simple relation names, plus any variables the relation
  // records as referenced (and likewise of its inner expression_or_dist). A
  // variable that only gates the constraint — for instance the antecedent p of
  // p -> soft q — is not among these, so 'disable soft' on such a variable
  // leaves the soft constraint in place, as the clause requires.
  auto directly_references = [](const ConstraintExpr& soft,
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
  };

  // Walk the soft constraints and 'disable soft' directives in declaration
  // order (every enabled block, then the inline constraints last) — the order
  // that fixes priority in 18.5.13.1. A directive discards the soft constraints
  // seen before it, which are exactly the ones of lower priority, that directly
  // reference the directive's variable.
  std::vector<const ConstraintExpr*> seen_soft;
  auto visit = [&](const ConstraintExpr& c) {
    if (c.kind == ConstraintKind::kSoft) {
      seen_soft.push_back(&c);
    } else if (c.kind == ConstraintKind::kDisableSoft) {
      for (const auto* s : seen_soft) {
        if (directly_references(*s, c.var_name)) disabled_soft_.insert(s);
      }
    }
  };
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) visit(c);
  }
  for (const auto& c : extra) visit(c);
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
  std::function<int(const std::string&, std::unordered_set<std::string>&)> dfs =
      [&](const std::string& v,
          std::unordered_set<std::string>& on_stack) -> int {
    auto cached = depth.find(v);
    if (cached != depth.end()) return cached->second;
    if (on_stack.count(v)) return 0;  // cycle guard (elaborator rejects cycles)
    on_stack.insert(v);
    int best = 0;
    auto it = succ.find(v);
    if (it != succ.end()) {
      for (const auto& w : it->second) {
        best = std::max(best, 1 + dfs(w, on_stack));
      }
    }
    on_stack.erase(v);
    depth[v] = best;
    return best;
  };
  int max_depth = 0;
  for (const auto& v : vars) {
    std::unordered_set<std::string> on_stack;
    max_depth = std::max(max_depth, dfs(v, on_stack));
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
  std::function<void(const std::string&)> dfs = [&](const std::string& v) {
    color[v] = 1;
    auto it = succ.find(v);
    if (it != succ.end()) {
      for (const auto& w : it->second) {
        if (color[w] == 1) {
          cycle = true;
          return;
        }
        if (color[w] == 0) {
          dfs(w);
          if (cycle) return;
        }
      }
    }
    color[v] = 2;
  };
  for (const auto& v : nodes) {
    if (color[v] == 0) {
      dfs(v);
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
  std::unordered_map<std::string, int> prank;
  for (const auto& v : vars) prank[v] = 0;
  // Iteratively relax: a successor's rank is at least one past its
  // predecessor's. The graph is acyclic here, so |vars| passes suffice to reach
  // the fixpoint.
  for (size_t pass = 0; pass < vars.size(); ++pass) {
    bool changed = false;
    for (const auto& [h, ls] : succ) {
      for (const auto& l : ls) {
        if (prank[l] < prank[h] + 1) {
          prank[l] = prank[h] + 1;
          changed = true;
        }
      }
    }
    if (!changed) break;
  }
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

bool ConstraintSolver::CheckCommittedConstraints(
    const std::vector<ConstraintExpr>& extra, bool include_soft,
    const std::unordered_set<std::string>& committed) const {
  std::vector<const ConstraintExpr*> hard;
  std::vector<const ConstraintExpr*> soft;
  CollectConstraints(blocks_, extra, hard, soft);
  auto ready = [&](const ConstraintExpr* c) {
    if (c->ref_vars.empty()) return false;  // checked only in the final pass
    for (const auto& v : c->ref_vars) {
      if (!committed.count(v)) return false;
    }
    return true;
  };
  for (const auto* c : hard) {
    if (!ready(c)) continue;
    if (!EvalConstraint(*c)) return false;
  }
  if (include_soft) {
    for (const auto* c : soft) {
      if (!ready(c)) continue;
      const ConstraintExpr* inner = c->inner ? c->inner : nullptr;
      if (inner && !EvalConstraint(*inner)) return false;
    }
  }
  return true;
}

bool ConstraintSolver::SolvePriorityLayers(
    const std::vector<std::vector<std::string>>& layers,
    const std::vector<ConstraintExpr>& extra, bool include_soft) {
  static constexpr int kLayerAttempts = 200;
  // committed starts from every variable already fixed before the general pass
  // — the inactive (state) variables, the randc draws, the array sizes, and the
  // real variables — all of which are present in values_/real_values_ by now.
  std::unordered_set<std::string> committed;
  for (const auto& kv : values_) committed.insert(kv.first);
  for (const auto& kv : real_values_) committed.insert(kv.first);
  for (const auto& layer : layers) {
    bool ok = false;
    for (int attempt = 0; attempt < kLayerAttempts; ++attempt) {
      for (const auto& name : layer) {
        auto it = variables_.find(name);
        if (it == variables_.end()) continue;
        values_[name] = GenerateRandValue(it->second);
      }
      std::unordered_set<std::string> with_layer = committed;
      for (const auto& name : layer) with_layer.insert(name);
      if (CheckCommittedConstraints(extra, include_soft, with_layer)) {
        ok = true;
        break;
      }
    }
    // 18.5.11: an earlier, higher-priority layer is never reconsidered. If no
    // draw of this layer satisfies the constraints that have become checkable,
    // the overall solve fails — the subdivision can make the set unsolvable.
    if (!ok) return false;
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
static bool RunStagedSolve(
    std::unordered_map<std::string, RandVariable>& variables,
    std::unordered_map<std::string, double>& real_values,
    const std::unordered_map<std::string, int64_t>& values, bool use_priority,
    const std::function<double(RandVariable&)>& gen_real,
    const std::function<std::vector<std::vector<std::string>>(
        const std::vector<std::string>&)>& partition,
    const std::function<bool(const std::vector<std::vector<std::string>>&)>&
        solve) {
  (void)use_priority;
  // Real variables are committed first (as in the flat pass), so any ordered
  // integral group/layer is completed against them.
  for (auto& [name, var] : variables) {
    if (var.enabled && var.is_real) {
      real_values[name] = gen_real(var);
    }
  }
  std::vector<std::string> general;
  for (auto& [name, var] : variables) {
    if (!var.enabled || var.is_real) continue;
    // randc, array-size, and inactive variables are already committed; the
    // cyclical ones in particular are solved first, as the clause requires.
    if (values.find(name) != values.end()) continue;
    general.push_back(name);
  }
  return solve(partition(general));
}

bool ConstraintSolver::SolveIterative(const std::vector<ConstraintExpr>& extra,
                                      bool include_soft) {
  static constexpr int kMaxAttempts = 500;
  guard_error_ = false;
  for (int attempt = 0; attempt < kMaxAttempts; ++attempt) {
    values_.clear();
    real_values_.clear();
    // 18.8 / 18.5.8: an inactive variable (rand_mode() OFF) is not one of the
    // active random variables, so it is not randomized. The solver instead
    // treats it as a state variable: its current value is seeded as a constant
    // before solving, so a global constraint relating it to an active variable
    // is evaluated against that fixed value rather than dropped.
    for (auto& [name, var] : variables_) {
      // 18.4.1: a real variable's value lives in real_values_, not the integral
      // values_ map; an inactive one likewise holds its current real value.
      if (var.is_real) {
        if (!var.enabled) real_values_[name] = var.real_value;
        continue;
      }
      if (!var.enabled) values_[name] = var.value;
    }
    ApplyDistConstraints();
    ApplyDirectConstraints(extra, include_soft);
    // 18.4.2: the cyclic (randc) variables shall be solved before the
    // noncyclical rand variables. Draw every active randc value first so that
    // the rand variables that follow are solved with the cyclic values already
    // committed for this attempt; a constraint set that mixes rand and randc
    // therefore resolves the randc variables first, as the cyclic semantics
    // require.
    for (auto& [name, var] : variables_) {
      if (!var.enabled || var.is_real) continue;
      if (var.qualifier != RandQualifier::kRandc) continue;
      if (values_.find(name) != values_.end()) continue;
      values_[name] = GenerateRandValue(var);
    }
    // 18.5.7.1: an array's size method is solved with the size constraints,
    // ahead of the iterative (foreach) constraints over that array. Commit
    // every active array-size variable here, before the general rand pass
    // below, so that a foreach reading the size sees the value already chosen
    // and treats it as a state variable rather than one it may itself
    // constrain. The general pass then skips these already-committed variables.
    for (auto& [name, var] : variables_) {
      if (!var.enabled || var.is_real) continue;
      if (!var.is_array_size) continue;
      if (var.qualifier == RandQualifier::kRandc) continue;
      if (values_.find(name) != values_.end()) continue;
      values_[name] = GenerateRandValue(var);
    }
    // 18.5.9: when a solve...before ordering applies, solve the active integral
    // rand variables in ordered groups rather than in one flat pass. An earlier
    // group is committed before the later groups are solved against it, which
    // shifts the probability distribution to match the ordering while leaving
    // the set of legal solutions unchanged. With no ordering the default single
    // pass below is used unchanged, and it already draws each legal value
    // combination with uniform probability. 18.5.11: when random variables are
    // used as function arguments, the implied priority is solved in layers —
    // the higher-priority variables first, each layer committed as state
    // variables to the next without backtracking. This subdivides the solution
    // space (and can fail), distinct from the solution-space-preserving
    // solve...before ordering handled below.
    if (!function_arg_priority_edges_.empty()) {
      if (RunStagedSolve(
              variables_, real_values_, values_, /*use_priority=*/true,
              [this](RandVariable& var) { return GenerateRandRealValue(var); },
              [this](const std::vector<std::string>& general) {
                return ComputePriorityLayers(general);
              },
              [&](const std::vector<std::vector<std::string>>& layers) {
                return SolvePriorityLayers(layers, extra, include_soft);
              })) {
        return true;
      }
      if (guard_error_) return false;
      continue;
    }
    if (!solve_before_edges_.empty()) {
      if (RunStagedSolve(
              variables_, real_values_, values_, /*use_priority=*/false,
              [this](RandVariable& var) { return GenerateRandRealValue(var); },
              [this](const std::vector<std::string>& general) {
                return ComputeSolveGroups(general);
              },
              [&](const std::vector<std::vector<std::string>>& groups) {
                return SolveOrderedGroups(groups, 0, extra, include_soft);
              })) {
        return true;
      }
      if (guard_error_) return false;
      continue;
    }
    for (auto& [name, var] : variables_) {
      if (!var.enabled) continue;
      // 18.4.1: draw an active real variable from its uniform real range.
      if (var.is_real) {
        real_values_[name] = GenerateRandRealValue(var);
        continue;
      }
      // randc variables are already committed above; skip them here.
      if (values_.find(name) != values_.end()) continue;
      values_[name] = GenerateRandValue(var);
    }
    if (CheckAllConstraints(extra, include_soft)) return true;
    // 18.5.12: an ERROR guard fails randomize() outright; do not retry it.
    if (guard_error_) return false;
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
