#include "simulation/constraint_solver.h"

#include <algorithm>
#include <cstdint>
#include <numeric>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

namespace delta {

ConstraintSolver::ConstraintSolver(uint32_t seed) : rng_(seed) {}

// §18.3: Register a rand/randc variable.
void ConstraintSolver::AddVariable(const RandVariable& var) {
  variables_[var.name] = var;
}

// §18.5: Add a named constraint block.
void ConstraintSolver::AddConstraintBlock(const ConstraintBlock& block) {
  blocks_.push_back(block);
}

// §18.8: rand_mode control.
void ConstraintSolver::SetRandMode(std::string_view name, bool enabled) {
  auto it = variables_.find(std::string(name));
  if (it != variables_.end()) it->second.enabled = enabled;
}

bool ConstraintSolver::GetRandMode(std::string_view name) const {
  auto it = variables_.find(std::string(name));
  return (it != variables_.end()) ? it->second.enabled : false;
}

// §18.9: constraint_mode control.
void ConstraintSolver::SetConstraintMode(std::string_view block_name,
                                         bool enabled) {
  for (auto& block : blocks_) {
    if (block.name == block_name) block.enabled = enabled;
  }
}

bool ConstraintSolver::GetConstraintMode(std::string_view block_name) const {
  for (const auto& block : blocks_) {
    if (block.name == block_name) return block.enabled;
  }
  return false;
}

// §18.7.2: Pre/post randomize hooks.
void ConstraintSolver::SetPreRandomize(RandomizeCallback cb) {
  pre_randomize_ = std::move(cb);
}

void ConstraintSolver::SetPostRandomize(RandomizeCallback cb) {
  post_randomize_ = std::move(cb);
}

const std::unordered_map<std::string, int64_t>& ConstraintSolver::GetValues()
    const {
  return values_;
}

// Generate a random value for a variable, respecting randc history.
int64_t ConstraintSolver::GenerateRandValue(RandVariable& var) {
  if (var.qualifier == RandQualifier::kRandc) {
    int64_t range_size = var.max_val - var.min_val + 1;
    // Reset cycle when all values have been used.
    if (static_cast<int64_t>(var.randc_history.size()) >= range_size) {
      var.randc_history.clear();
    }
    // Try random values not in history.
    for (int attempt = 0; attempt < 1000; ++attempt) {
      std::uniform_int_distribution<int64_t> dist(var.min_val, var.max_val);
      int64_t val = dist(rng_);
      if (var.randc_history.find(val) == var.randc_history.end()) {
        var.randc_history.insert(val);
        return val;
      }
    }
    // Fallback: linear scan for remaining values.
    for (int64_t v = var.min_val; v <= var.max_val; ++v) {
      if (var.randc_history.find(v) == var.randc_history.end()) {
        var.randc_history.insert(v);
        return v;
      }
    }
    var.randc_history.clear();
    var.randc_history.insert(var.min_val);
    return var.min_val;
  }
  std::uniform_int_distribution<int64_t> dist(var.min_val, var.max_val);
  return dist(rng_);
}

// §18.5.4: Weighted random selection.
int64_t ConstraintSolver::DistributionSample(
    const std::vector<DistWeight>& weights) {
  if (weights.empty()) return 0;
  uint64_t total = 0;
  for (const auto& w : weights) total += w.weight;
  if (total == 0) return weights[0].value;

  std::uniform_int_distribution<uint64_t> dist(0, total - 1);
  uint64_t pick = dist(rng_);
  uint64_t accum = 0;
  for (const auto& w : weights) {
    accum += w.weight;
    if (pick < accum) return w.value;
  }
  return weights.back().value;
}

// Evaluate a range constraint: lo <= var <= hi.
static bool EvalRange(int64_t val, int64_t lo, int64_t hi) {
  return val >= lo && val <= hi;
}

// Evaluate a set-membership constraint: var inside {v1, v2, ...}.
static bool EvalSetMembership(int64_t val,
                              const std::vector<int64_t>& set_values) {
  for (int64_t v : set_values) {
    if (val == v) return true;
  }
  return false;
}

// Evaluate a comparison constraint against the variable's current value.
static bool EvalComparison(ConstraintKind kind, int64_t val, int64_t target) {
  switch (kind) {
    case ConstraintKind::kEqual:
      return val == target;
    case ConstraintKind::kNotEqual:
      return val != target;
    case ConstraintKind::kLessThan:
      return val < target;
    case ConstraintKind::kGreaterThan:
      return val > target;
    case ConstraintKind::kLessEqual:
      return val <= target;
    case ConstraintKind::kGreaterEqual:
      return val >= target;
    default:
      return true;
  }
}

// Evaluate a single constraint against current values.
bool ConstraintSolver::EvalConstraint(const ConstraintExpr& expr) const {
  switch (expr.kind) {
    case ConstraintKind::kRange: {
      auto it = values_.find(expr.var_name);
      if (it == values_.end()) return true;
      return EvalRange(it->second, expr.lo, expr.hi);
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
      return EvalComparison(expr.kind, it->second, expr.lo);
    }
    case ConstraintKind::kImplication:
      return EvalImplication(expr);
    case ConstraintKind::kForeach:
      return EvalForeach(expr);
    case ConstraintKind::kUnique:
      return EvalUnique(expr);
    case ConstraintKind::kDist:
    case ConstraintKind::kSoft:
      // Dist is applied during generation; soft constraints are best-effort.
      return true;
    case ConstraintKind::kCustom:
      return expr.eval_fn ? expr.eval_fn(values_) : true;
  }
  return true;
}

// Apply a single constraint to narrow or set a variable's value.
bool ConstraintSolver::ApplyConstraint(const ConstraintExpr& expr) {
  if (expr.kind == ConstraintKind::kDist) {
    values_[expr.var_name] = DistributionSample(expr.dist_weights);
    return true;
  }
  return EvalConstraint(expr);
}

// Collect all hard constraints from enabled blocks + inline extras.
static void CollectConstraints(const std::vector<ConstraintBlock>& blocks,
                               const std::vector<ConstraintExpr>& extra,
                               std::vector<const ConstraintExpr*>& hard,
                               std::vector<const ConstraintExpr*>& soft) {
  for (const auto& block : blocks) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (c.kind == ConstraintKind::kSoft) {
        soft.push_back(&c);
      } else {
        hard.push_back(&c);
      }
    }
  }
  for (const auto& c : extra) {
    if (c.kind == ConstraintKind::kSoft) {
      soft.push_back(&c);
    } else {
      hard.push_back(&c);
    }
  }
}

// Check if current values satisfy all hard constraints.
bool ConstraintSolver::CheckAllConstraints(
    const std::vector<ConstraintExpr>& extra) {
  std::vector<const ConstraintExpr*> hard;
  std::vector<const ConstraintExpr*> soft;
  CollectConstraints(blocks_, extra, hard, soft);
  for (const auto* c : hard) {
    if (!EvalConstraint(*c)) return false;
  }
  return true;
}

// §18.5.6: Implication evaluation.
bool ConstraintSolver::EvalImplication(const ConstraintExpr& expr) const {
  auto it = values_.find(expr.cond_var);
  if (it == values_.end()) return true;
  if (it->second != expr.cond_value) return true;
  for (const auto& sub : expr.sub_constraints) {
    if (!EvalConstraint(sub)) return false;
  }
  return true;
}

// §18.5.7: Foreach evaluation (simplified).
bool ConstraintSolver::EvalForeach(const ConstraintExpr& expr) const {
  for (const auto& sub : expr.sub_constraints) {
    if (!EvalConstraint(sub)) return false;
  }
  return true;
}

// §18.5.5: Unique constraint evaluation.
bool ConstraintSolver::EvalUnique(const ConstraintExpr& expr) const {
  std::unordered_set<int64_t> seen;
  for (const auto& vname : expr.unique_vars) {
    auto it = values_.find(vname);
    if (it == values_.end()) continue;
    if (seen.count(it->second)) return false;
    seen.insert(it->second);
  }
  return true;
}

// §18.7: Main solve entry point.
bool ConstraintSolver::Solve() { return SolveWith({}); }

// Apply equality/set-membership constraints directly for fast convergence.
void ConstraintSolver::ApplyDirectConstraints(
    const std::vector<ConstraintExpr>& extra) {
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
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) apply(c);
  }
  for (const auto& c : extra) apply(c);
}

// §18.7.1: Solve with inline constraints.
bool ConstraintSolver::SolveWith(
    const std::vector<ConstraintExpr>& inline_constraints) {
  if (pre_randomize_) pre_randomize_();

  // Clear previous solution.
  values_.clear();

  // Apply distribution constraints first.
  ApplyDistConstraints();

  // Apply direct-assignment constraints (equality, set membership).
  ApplyDirectConstraints(inline_constraints);

  // Generate random values for remaining enabled variables.
  for (auto& [name, var] : variables_) {
    if (!var.enabled) continue;
    if (values_.find(name) != values_.end()) continue;
    values_[name] = GenerateRandValue(var);
  }

  // Iterative constraint solving with backtracking.
  bool solved = SolveIterative(inline_constraints);

  if (solved && post_randomize_) post_randomize_();
  return solved;
}

// Apply all dist constraints to set initial values.
void ConstraintSolver::ApplyDistConstraints() {
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (c.kind == ConstraintKind::kDist) {
        values_[c.var_name] = DistributionSample(c.dist_weights);
      }
    }
  }
}

// Iterative solving: try to satisfy constraints with limited backtracking.
bool ConstraintSolver::SolveIterative(
    const std::vector<ConstraintExpr>& extra) {
  static constexpr int kMaxAttempts = 500;
  for (int attempt = 0; attempt < kMaxAttempts; ++attempt) {
    if (CheckAllConstraints(extra)) return true;
    // Re-randomize and retry.
    values_.clear();
    ApplyDistConstraints();
    ApplyDirectConstraints(extra);
    for (auto& [name, var] : variables_) {
      if (!var.enabled) continue;
      if (values_.find(name) != values_.end()) continue;
      values_[name] = GenerateRandValue(var);
    }
  }
  return false;
}

// §18.7: Get solved value.
int64_t ConstraintSolver::GetValue(std::string_view name) const {
  auto it = values_.find(std::string(name));
  return (it != values_.end()) ? it->second : 0;
}

}  // namespace delta
