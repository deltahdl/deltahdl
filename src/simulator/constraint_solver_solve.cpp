#include <algorithm>
#include <cstddef>
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

constexpr int kRepairFromAttempt = 32;

int SolveGroupDepth(
    const std::string& v,
    const std::unordered_map<std::string, std::vector<std::string>>& succ,
    std::unordered_map<std::string, int>& depth,
    std::unordered_set<std::string>& on_stack) {
  auto cached = depth.find(v);
  if (cached != depth.end()) return cached->second;
  if (on_stack.count(v)) return 0;
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

}  // namespace

void SeedInactiveVariables(
    std::unordered_map<std::string, RandVariable>& variables,
    std::unordered_map<std::string, int64_t>& values,
    std::unordered_map<std::string, double>& real_values) {
  for (auto& [name, var] : variables) {
    if (var.is_real) {
      if (!var.enabled) real_values[name] = var.real_value;
      continue;
    }
    if (!var.enabled) values[name] = var.value;
  }
}

namespace {

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

void DrawGeneralPass(std::unordered_map<std::string, RandVariable>& variables,
                     std::unordered_map<std::string, int64_t>& values,
                     std::unordered_map<std::string, double>& real_values,
                     const std::function<int64_t(RandVariable&)>& gen,
                     const std::function<double(RandVariable&)>& gen_real) {
  for (auto& [name, var] : variables) {
    if (!var.enabled) continue;
    if (var.is_real) {
      if (real_values.find(name) == real_values.end())
        real_values[name] = gen_real(var);
      continue;
    }
    if (values.find(name) != values.end()) continue;
    values[name] = gen(var);
  }
}

bool ConstraintReady(const ConstraintExpr& c,
                     const std::unordered_set<std::string>& committed) {
  if (c.ref_vars.empty()) return false;
  for (const auto& v : c.ref_vars) {
    if (!committed.count(v)) return false;
  }
  return true;
}

}  // namespace

void ApplyConcreteConstraint(const ConstraintExpr& c,
                             std::unordered_map<std::string, int64_t>& values,
                             std::mt19937& rng, bool holds_state_value) {
  if (holds_state_value) return;
  if (c.kind == ConstraintKind::kEqual) {
    values[c.var_name] = c.lo;
  } else if (c.kind == ConstraintKind::kSetMembership) {
    if (!c.set_values.empty()) {
      std::uniform_int_distribution<size_t> pick(0, c.set_values.size() - 1);
      values[c.var_name] = c.set_values[pick(rng)];
    }
  }
}

bool ConstraintSolver::Solve() { return SolveWith({}); }

bool ConstraintSolver::Check(const std::vector<ConstraintExpr>& constraints) {
  guard_error_ = false;
  RefreshStaticBlockState();
  for (const auto& [name, var] : variables_) {
    values_[name] = var.value;
  }
  return CheckAllConstraints(constraints, true);
}

void ConstraintSolver::ApplyDirectConstraints(
    const std::vector<ConstraintExpr>& extra, bool include_soft) {
  auto seed = [&](const ConstraintExpr& c) {
    if (SoftSeedApplies(c, include_soft)) {
      SeedHonoredSoft(*c.inner, extra);
      return;
    }
    auto vit = variables_.find(c.var_name);
    bool randc = vit != variables_.end() && vit->second.enabled &&
                 vit->second.qualifier == RandQualifier::kRandc;
    ApplyConcreteConstraint(c, values_, rng_,
                            HoldsStateValue(c.var_name) || randc);
  };
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) seed(c);
  }
  for (const auto& c : extra) seed(c);
}

bool ConstraintSolver::SolveWith(
    const std::vector<ConstraintExpr>& inline_constraints) {
  RefreshStaticBlockState();

  if (DistLacksRandVariable()) return false;

  if (HasRandcInUnique()) return false;
  if (UniqueMembersNotEquivalentType()) return false;

  if (HasFunctionArgPriorityCycle()) return false;

  if (pre_randomize_) pre_randomize_();

  if (HasEmptyDomain()) return false;

  const std::unordered_map<std::string, int64_t> kPrevValues = values_;
  const std::unordered_map<std::string, double> kPrevRealValues = real_values_;

  ComputeDisabledSoft(inline_constraints);

  dropped_soft_.clear();
  guard_error_ = false;
  bool solved = !HonoredBoundsConflict(inline_constraints) &&
                SolveIterative(inline_constraints, true);

  if (!solved && !guard_error_) {
    solved = SolveBySoftPriority(inline_constraints);
  }

  dropped_soft_.clear();
  disabled_soft_.clear();

  if (solved) {
    CommitStaticSharedValues();
  } else {
    values_ = kPrevValues;
    real_values_ = kPrevRealValues;
  }

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

void ConstraintSolver::ApplyDistConstraints(
    const std::vector<ConstraintExpr>& extra) {
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (c.kind == ConstraintKind::kDist) {
        if (HoldsStateValue(c.var_name)) continue;
        SeedDist(c, extra);
      }
    }
  }
}

std::vector<std::vector<std::string>> ConstraintSolver::ComputeSolveGroups(
    const std::vector<std::string>& vars) const {
  std::unordered_set<std::string> var_set(vars.begin(), vars.end());
  std::unordered_map<std::string, std::vector<std::string>> succ;
  for (const auto& [b, a] : solve_before_edges_) {
    if (var_set.count(b) && var_set.count(a)) succ[b].push_back(a);
  }
  std::unordered_map<std::string, int> depth;
  int max_depth = 0;
  for (const auto& v : vars) {
    std::unordered_set<std::string> on_stack;
    max_depth = std::max(max_depth, SolveGroupDepth(v, succ, depth, on_stack));
  }
  std::vector<std::vector<std::string>> buckets(max_depth + 1);
  for (const auto& v : vars) buckets[max_depth - depth[v]].push_back(v);
  std::vector<std::vector<std::string>> groups;
  for (auto& g : buckets) {
    if (!g.empty()) groups.push_back(std::move(g));
  }
  return groups;
}

void ConstraintSolver::RepairWithin(const std::vector<std::string>& names,
                                    const std::vector<ConstraintExpr>& extra) {
  repair_scope_.insert(names.begin(), names.end());
  RepairConstraints(extra);
  repair_scope_.clear();
}

bool ConstraintSolver::SolveOrderedGroups(
    const std::vector<std::vector<std::string>>& groups, size_t idx,
    const std::vector<ConstraintExpr>& extra, bool include_soft) {
  if (idx == groups.size()) return CheckAllConstraints(extra, include_soft);
  static constexpr int kGroupAttempts = 200;
  const bool kLast = idx + 1 == groups.size();
  for (int attempt = 0; attempt < kGroupAttempts; ++attempt) {
    for (const auto& name : groups[idx]) {
      auto it = variables_.find(name);
      if (it == variables_.end()) continue;
      values_[name] = GenerateRandValue(it->second);
    }
    if (kLast && attempt >= kRepairFromAttempt)
      RepairWithin(groups[idx], extra);
    if (SolveOrderedGroups(groups, idx + 1, extra, include_soft)) return true;
    if (guard_error_) return false;
  }
  return false;
}

bool ConstraintSolver::HasFunctionArgPriorityCycle() const {
  std::unordered_map<std::string, std::vector<std::string>> succ;
  std::unordered_set<std::string> nodes;
  for (const auto& [h, l] : function_arg_priority_edges_) {
    succ[h].push_back(l);
    nodes.insert(h);
    nodes.insert(l);
  }
  std::unordered_map<std::string, int> color;
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
  std::unordered_map<std::string, std::vector<std::string>> succ;
  for (const auto& [h, l] : function_arg_priority_edges_) {
    if (var_set.count(h) && var_set.count(l)) succ[h].push_back(l);
  }
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

std::unordered_set<std::string> CommittedFromValues(
    const std::unordered_map<std::string, int64_t>& values,
    const std::unordered_map<std::string, double>& real_values) {
  std::unordered_set<std::string> committed;
  for (const auto& kv : values) committed.insert(kv.first);
  for (const auto& kv : real_values) committed.insert(kv.first);
  return committed;
}

}  // namespace

void ConstraintSolver::RepairReadyWithin(
    const std::vector<std::string>& names,
    const std::unordered_set<std::string>& committed,
    const std::vector<ConstraintExpr>& extra) {
  std::vector<const ConstraintExpr*> hard;
  std::vector<const ConstraintExpr*> soft;
  CollectConstraints(blocks_, extra, hard, soft);
  repair_scope_.insert(names.begin(), names.end());
  repair_extra_ = &extra;
  for (const auto* c : hard) {
    if (ConstraintReady(*c, committed)) RepairConstraint(*c);
  }
  repair_extra_ = nullptr;
  repair_scope_.clear();
}

bool ConstraintSolver::DrawPriorityLayer(
    const std::vector<std::string>& layer,
    const std::unordered_set<std::string>& committed,
    const std::vector<ConstraintExpr>& extra, bool include_soft) {
  static constexpr int kLayerAttempts = 200;
  std::unordered_set<std::string> with_layer = committed;
  for (const auto& name : layer) with_layer.insert(name);
  for (int attempt = 0; attempt < kLayerAttempts; ++attempt) {
    for (const auto& name : layer) {
      auto it = variables_.find(name);
      if (it == variables_.end()) continue;
      values_[name] = GenerateRandValue(it->second);
    }
    if (attempt >= kRepairFromAttempt)
      RepairReadyWithin(layer, with_layer, extra);
    if (CheckCommittedConstraints(extra, include_soft, with_layer)) return true;
  }
  return false;
}

bool ConstraintSolver::SolvePriorityLayers(
    const std::vector<std::vector<std::string>>& layers,
    const std::vector<ConstraintExpr>& extra, bool include_soft) {
  std::unordered_set<std::string> committed =
      CommittedFromValues(values_, real_values_);
  for (const auto& layer : layers) {
    if (!DrawPriorityLayer(layer, committed, extra, include_soft)) return false;
    for (const auto& name : layer) committed.insert(name);
  }
  return CheckAllConstraints(extra, include_soft);
}

static void CommitStagedRealVariables(
    std::unordered_map<std::string, RandVariable>& variables,
    std::unordered_map<std::string, double>& real_values,
    const std::function<double(RandVariable&)>& gen_real) {
  for (auto& [name, var] : variables) {
    if (var.enabled && var.is_real &&
        real_values.find(name) == real_values.end()) {
      real_values[name] = gen_real(var);
    }
  }
}

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

enum class AttemptOutcome : std::uint8_t {
  kSolved,
  kAbort,
  kRetry,
};

AttemptOutcome ResolveAttempt(const std::function<bool()>& pass,
                              const bool& guard_error) {
  if (pass()) return AttemptOutcome::kSolved;
  if (guard_error) return AttemptOutcome::kAbort;
  return AttemptOutcome::kRetry;
}

struct AttemptPasses {
  const std::function<bool()>& priority;
  const std::function<bool()>& ordered;
  const std::function<bool()>& flat;
};

AttemptOutcome RunAttemptPass(bool has_priority_edges, bool has_before_edges,
                              const AttemptPasses& passes,
                              const bool& guard_error) {
  if (has_priority_edges) return ResolveAttempt(passes.priority, guard_error);
  if (has_before_edges) return ResolveAttempt(passes.ordered, guard_error);
  return ResolveAttempt(passes.flat, guard_error);
}

}  // namespace

void ConstraintSolver::SeedAttempt(
    const std::vector<ConstraintExpr>& extra, bool include_soft, bool repair,
    const std::unordered_map<std::string, int64_t>& sizes,
    const std::function<int64_t(RandVariable&)>& gen_randc) {
  auto gen = [this](RandVariable& var) { return GenerateRandValue(var); };
  values_.clear();
  real_values_.clear();
  SeedInactiveVariables(variables_, values_, real_values_);
  ApplyDistConstraints(extra);
  ApplyDirectConstraints(extra, include_soft);
  if (!repair) SeedSoftBounds(extra, include_soft);
  HoldArraySizes(sizes);
  DrawRandcVariables(variables_, values_, gen_randc);
  DrawArraySizeVariables(variables_, values_, gen);
  SeedEnumerableVariables(extra, enumerated_);
}

bool ConstraintSolver::FlatPass(
    const std::vector<ConstraintExpr>& extra, bool include_soft, bool repair,
    const std::function<int64_t(RandVariable&)>& gen,
    const std::function<double(RandVariable&)>& gen_real) {
  if (repair) DrawPropagated(extra);
  DrawGeneralPass(variables_, values_, real_values_, gen, gen_real);
  if (repair) RepairConstraints(extra);
  return CheckAllConstraints(extra, include_soft);
}

bool ConstraintSolver::SolveIterative(const std::vector<ConstraintExpr>& extra,
                                      bool include_soft) {
  static constexpr int kMaxAttempts = 500;
  guard_error_ = false;
  auto gen = [this](RandVariable& var) { return GenerateRandValue(var); };
  const std::unordered_map<std::string, int64_t> kSizes =
      DrawArraySizesOnce(extra, include_soft, gen);
  auto gen_real = [this](RandVariable& var) {
    return GenerateRandRealValue(var);
  };
  std::unordered_map<std::string, int64_t> randc_drawn;
  auto gen_randc = RandcOncePerSolve(randc_drawn, extra);
  enumerated_.clear();
  StagedSolveState state{variables_, real_values_, values_};
  auto priority_pass = [&] {
    return RunStagedSolve(
        state, true, gen_real,
        [this](const std::vector<std::string>& general) {
          return ComputePriorityLayers(general);
        },
        [&](const std::vector<std::vector<std::string>>& layers) {
          return SolvePriorityLayers(layers, extra, include_soft);
        });
  };
  auto ordered_pass = [&] {
    return RunStagedSolve(
        state, false, gen_real,
        [this](const std::vector<std::string>& general) {
          return ComputeSolveGroups(general);
        },
        [&](const std::vector<std::vector<std::string>>& groups) {
          return SolveOrderedGroups(groups, 0, extra, include_soft);
        });
  };
  bool repair = false;
  auto flat_pass = [&] {
    return FlatPass(extra, include_soft, repair, gen, gen_real);
  };
  for (int attempt = 0; attempt < kMaxAttempts; ++attempt) {
    repair = attempt >= kRepairFromAttempt;
    SeedAttempt(extra, include_soft, repair, kSizes, gen_randc);
    AttemptPasses passes{priority_pass, ordered_pass, flat_pass};
    AttemptOutcome outcome =
        RunAttemptPass(!function_arg_priority_edges_.empty(),
                       !solve_before_edges_.empty(), passes, guard_error_);
    if (outcome == AttemptOutcome::kSolved) return true;
    if (outcome == AttemptOutcome::kAbort) return false;
    PruneRefusedRandcValues(randc_drawn, extra);
  }
  return false;
}

int64_t ConstraintSolver::GetValue(std::string_view name) const {
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
