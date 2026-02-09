#pragma once

#include <cstdint>
#include <functional>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace delta {

// §18.3: Random variable qualifier.
enum class RandQualifier : uint8_t {
  kNone,
  kRand,   // §18.3: random permutation
  kRandc,  // §18.4: cyclic random
};

// §18.5: Constraint expression kind.
enum class ConstraintKind : uint8_t {
  kRange,          // §18.5.3: inside {lo:hi}
  kSetMembership,  // §18.5.3: inside {v1, v2, ...}
  kEqual,          // var == expr
  kNotEqual,       // var != expr
  kLessThan,       // var < expr
  kGreaterThan,    // var > expr
  kLessEqual,      // var <= expr
  kGreaterEqual,   // var >= expr
  kImplication,    // §18.5.6: cond -> {constraints}
  kForeach,        // §18.5.7: foreach constraint
  kUnique,         // §18.5.5: unique {vars}
  kDist,           // §18.5.4: dist {val := weight}
  kSoft,           // §18.5.13: soft constraint
  kCustom,         // Evaluated via callback
};

// §18.5.4: Distribution weight entry.
struct DistWeight {
  int64_t value = 0;
  uint32_t weight = 1;
};

// §18.5: Single constraint expression.
struct ConstraintExpr {
  ConstraintKind kind = ConstraintKind::kRange;
  std::string var_name;
  int64_t lo = 0;
  int64_t hi = 0;
  std::vector<int64_t> set_values;
  std::vector<DistWeight> dist_weights;
  // §18.5.6: Implication — condition variable and threshold.
  std::string cond_var;
  int64_t cond_value = 0;
  std::vector<ConstraintExpr> sub_constraints;
  // §18.5.5: Unique variable names.
  std::vector<std::string> unique_vars;
  // §18.5.13: Soft flag (embedded in kind == kSoft).
  ConstraintExpr* inner = nullptr;
  // §18.5: Custom evaluator for inline constraints.
  std::function<bool(const std::unordered_map<std::string, int64_t>&)> eval_fn;
};

// §18.5: Named constraint block.
struct ConstraintBlock {
  std::string name;
  bool enabled = true;  // §18.9: constraint_mode
  std::vector<ConstraintExpr> constraints;
};

// §18.3-18.4: Random variable descriptor.
struct RandVariable {
  std::string name;
  RandQualifier qualifier = RandQualifier::kRand;
  int64_t min_val = 0;
  int64_t max_val = 0xFFFF;
  uint32_t width = 32;
  bool enabled = true;  // §18.8: rand_mode
  // §18.4: randc history for cyclic behavior.
  std::unordered_set<int64_t> randc_history;
};

// §18.7.2: Pre/post randomize callback.
using RandomizeCallback = std::function<void()>;

// §18: Constraint solver — BFS domain-reduction with backtracking.
class ConstraintSolver {
 public:
  explicit ConstraintSolver(uint32_t seed = 0);

  // §18.3: Register a rand/randc variable.
  void AddVariable(const RandVariable& var);

  // §18.5: Add a named constraint block.
  void AddConstraintBlock(const ConstraintBlock& block);

  // §18.7: Solve all constraints. Returns true if satisfiable.
  bool Solve();

  // §18.7.1: Solve with additional inline constraints.
  bool SolveWith(const std::vector<ConstraintExpr>& inline_constraints);

  // §18.7: Get solved value for a variable.
  int64_t GetValue(std::string_view name) const;

  // §18.8: rand_mode enable/disable.
  void SetRandMode(std::string_view name, bool enabled);
  bool GetRandMode(std::string_view name) const;

  // §18.9: constraint_mode enable/disable.
  void SetConstraintMode(std::string_view block_name, bool enabled);
  bool GetConstraintMode(std::string_view block_name) const;

  // §18.7.2: Pre/post randomize hooks.
  void SetPreRandomize(RandomizeCallback cb);
  void SetPostRandomize(RandomizeCallback cb);

  // Access to solved values map (for custom evaluator).
  const std::unordered_map<std::string, int64_t>& GetValues() const;

 private:
  // Generate random value within [min, max] respecting randc history.
  int64_t GenerateRandValue(RandVariable& var);

  // §18.5.4: Weighted random selection from distribution.
  int64_t DistributionSample(const std::vector<DistWeight>& weights);

  // Apply a single constraint, narrowing the domain. Returns false on fail.
  bool ApplyConstraint(const ConstraintExpr& expr);

  // Check if current assignment satisfies all hard constraints.
  bool CheckAllConstraints(const std::vector<ConstraintExpr>& extra);

  // Check a single constraint expression.
  bool EvalConstraint(const ConstraintExpr& expr) const;

  // §18.5.6: Evaluate implication constraint.
  bool EvalImplication(const ConstraintExpr& expr) const;

  // §18.5.7: Evaluate foreach constraint.
  bool EvalForeach(const ConstraintExpr& expr) const;

  // §18.5.5: Evaluate unique constraint.
  bool EvalUnique(const ConstraintExpr& expr) const;

  // Apply all distribution constraints to set initial values.
  void ApplyDistConstraints();

  // Apply equality/set-membership constraints directly.
  void ApplyDirectConstraints(const std::vector<ConstraintExpr>& extra);

  // Iterative solving with backtracking.
  bool SolveIterative(const std::vector<ConstraintExpr>& extra);

  std::mt19937 rng_;
  std::unordered_map<std::string, RandVariable> variables_;
  std::vector<ConstraintBlock> blocks_;
  std::unordered_map<std::string, int64_t> values_;
  RandomizeCallback pre_randomize_;
  RandomizeCallback post_randomize_;
};

}  // namespace delta
