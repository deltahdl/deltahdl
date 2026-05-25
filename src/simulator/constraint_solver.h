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

enum class RandQualifier : uint8_t {
  kNone,
  kRand,
  kRandc,
};

enum class ConstraintKind : uint8_t {
  kRange,
  kSetMembership,
  kEqual,
  kNotEqual,
  kLessThan,
  kGreaterThan,
  kLessEqual,
  kGreaterEqual,
  kImplication,
  kForeach,
  kUnique,
  kDist,
  kSoft,
  kCustom,
};

struct DistWeight {
  int64_t value = 0;
  uint32_t weight = 1;
};

struct ConstraintExpr {
  ConstraintKind kind = ConstraintKind::kRange;
  std::string var_name;
  int64_t lo = 0;
  int64_t hi = 0;
  std::vector<int64_t> set_values;
  std::vector<DistWeight> dist_weights;

  std::string cond_var;
  int64_t cond_value = 0;
  std::vector<ConstraintExpr> sub_constraints;

  std::vector<std::string> unique_vars;

  ConstraintExpr* inner = nullptr;

  std::function<bool(const std::unordered_map<std::string, int64_t>&)> eval_fn;
};

struct ConstraintBlock {
  std::string name;
  bool enabled = true;
  std::vector<ConstraintExpr> constraints;
};

struct RandVariable {
  std::string name;
  RandQualifier qualifier = RandQualifier::kRand;
  int64_t min_val = 0;
  int64_t max_val = 0xFFFF;
  uint32_t width = 32;
  bool enabled = true;

  // 18.3: for an active random variable of enum type, the solver shall select
  // a value only from the set of named constants of that enum. When non-empty,
  // enum_values is that named-constant set and confines the chosen value.
  std::vector<int64_t> enum_values;

  // 18.4: an enum member of a packed structure or packed untagged union that
  // is declared rand is exempt from the 18.3 enum-domain restriction. Clearing
  // this flag keeps the enum_values set for reference but lets the solver draw
  // from the full declared range.
  bool apply_enum_restriction = true;

  std::unordered_set<int64_t> randc_history;
};

using RandomizeCallback = std::function<void()>;

class ConstraintSolver {
 public:
  explicit ConstraintSolver(uint32_t seed = 0);

  void AddVariable(const RandVariable& var);

  void AddConstraintBlock(const ConstraintBlock& block);

  bool Solve();

  bool SolveWith(const std::vector<ConstraintExpr>& inline_constraints);

  int64_t GetValue(std::string_view name) const;

  void SetRandMode(std::string_view name, bool enabled);
  bool GetRandMode(std::string_view name) const;

  void SetConstraintMode(std::string_view block_name, bool enabled);
  bool GetConstraintMode(std::string_view block_name) const;

  void SetPreRandomize(RandomizeCallback cb);
  void SetPostRandomize(RandomizeCallback cb);

  const std::unordered_map<std::string, int64_t>& GetValues() const;

 private:

  int64_t GenerateRandValue(RandVariable& var);

  int64_t DistributionSample(const std::vector<DistWeight>& weights);

  bool ApplyConstraint(const ConstraintExpr& expr);

  bool CheckAllConstraints(const std::vector<ConstraintExpr>& extra);

  bool EvalConstraint(const ConstraintExpr& expr) const;

  bool EvalImplication(const ConstraintExpr& expr) const;

  bool EvalForeach(const ConstraintExpr& expr) const;

  bool EvalUnique(const ConstraintExpr& expr) const;

  void ApplyDistConstraints();

  void ApplyDirectConstraints(const std::vector<ConstraintExpr>& extra);

  bool SolveIterative(const std::vector<ConstraintExpr>& extra);

  std::mt19937 rng_;
  std::unordered_map<std::string, RandVariable> variables_;
  std::vector<ConstraintBlock> blocks_;
  std::unordered_map<std::string, int64_t> values_;
  RandomizeCallback pre_randomize_;
  RandomizeCallback post_randomize_;
};

}
