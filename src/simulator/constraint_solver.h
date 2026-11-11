#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
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

bool ValueLess(bool is_signed, int64_t a, int64_t b);

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
  kIfElse,
  kForeach,
  kUnique,
  kDist,
  kSoft,
  kDisableSoft,
  kArrayReduction,
  kCustom,
};

enum class ArrayReductionOp : uint8_t {
  kSum,
  kProduct,
  kAnd,
  kOr,
  kXor,
};

struct DistWeight {
  int64_t value = 0;
  uint64_t weight = 1;
  int64_t lo = 0;
  int64_t hi = 0;
  double real_value = 0.0;
  double real_lo = 0.0;
  double real_hi = 0.0;
  bool is_range = false;
  bool per_element = false;
  bool is_default = false;
};

enum class GuardValue : uint8_t {
  kFalse,
  kTrue,
  kError,
  kRandom,
};

GuardValue GuardAnd(GuardValue a, GuardValue b);
GuardValue GuardOr(GuardValue a, GuardValue b);
GuardValue GuardNot(GuardValue a);

enum class GuardOutcome : uint8_t {
  kUnconditional,
  kEliminated,
  kError,
  kConditional,
};

GuardOutcome GuardFinalOutcome(GuardValue final_value);

struct GuardPredicate {
  enum class Op : uint8_t { kLeaf, kAnd, kOr, kNot } op = Op::kLeaf;
  std::function<GuardValue(const std::unordered_map<std::string, int64_t>&)>
      leaf_fn;
  std::vector<GuardPredicate> operands;
};

GuardValue EvaluateGuard(
    const GuardPredicate& pred,
    const std::unordered_map<std::string, int64_t>& values);

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

  std::string size_var;

  std::function<bool(const std::unordered_map<std::string, int64_t>&)> cond_fn;

  std::vector<ConstraintExpr> else_constraints;

  std::vector<std::string> unique_vars;

  ArrayReductionOp reduce_op = ArrayReductionOp::kSum;
  std::vector<std::string> reduce_vars;
  std::function<int64_t(int64_t)> reduce_with;
  ConstraintKind reduce_cmp = ConstraintKind::kLessThan;
  uint32_t reduce_width = 32;

  ConstraintExpr* inner = nullptr;

  std::function<bool(const std::unordered_map<std::string, int64_t>&)> eval_fn;
  std::function<int64_t(const std::unordered_map<std::string, int64_t>&)>
      derive_fn;
  ConstraintKind derive_cmp = ConstraintKind::kEqual;
  std::string co_var_name;

  std::vector<std::string> ref_vars;

  bool has_guard = false;
  GuardPredicate guard;
};

struct ConstraintBlock {
  std::string name;
  bool enabled = true;
  std::vector<ConstraintExpr> constraints;

  bool is_static = false;
  std::shared_ptr<bool> shared_enabled;
};

struct RandVariable {
  std::string name;
  RandQualifier qualifier = RandQualifier::kRand;
  int64_t min_val = 0;
  int64_t max_val = 0xFFFF;
  uint32_t width = 32;

  bool is_signed = true;

  void BindDomainToDeclaredRange();

  bool DomainLess(int64_t a, int64_t b) const;
  int64_t DomainMin(int64_t a, int64_t b) const;
  int64_t DomainMax(int64_t a, int64_t b) const;

  void CollapseEmptyDomain();
  bool domain_empty = false;

  uint64_t DomainSize() const;

  int64_t DrawUniform(std::mt19937& rng) const;

  int64_t ValueFromBits(uint64_t bits) const;

  bool is_real = false;
  double real_min = 0.0;
  double real_max = 0.0;
  double real_value = 0.0;

  bool enabled = true;

  int64_t value = 0;

  std::vector<int64_t> enum_values;

  bool apply_enum_restriction = true;

  std::unordered_set<int64_t> randc_history;

  bool is_static = false;
  std::shared_ptr<std::unordered_set<int64_t>> shared_randc_state;

  std::vector<int64_t> randc_domain;
  std::shared_ptr<std::vector<int64_t>> shared_randc_domain;

  std::shared_ptr<int64_t> shared_value;

  bool is_array_size = false;
};

using RandomizeCallback = std::function<void()>;

class ConstraintSolver {
 public:
  explicit ConstraintSolver(uint32_t seed = 0);

  void SetNameScope(std::string prefix);

  void AddVariable(const RandVariable& var);

  const RandVariable* FindVariable(std::string_view name) const;

  void AddConstraintBlock(const ConstraintBlock& block);

  void AddSolveBefore(const std::vector<std::string>& before,
                      const std::vector<std::string>& after);

  void AddFunctionArgPriority(const std::vector<std::string>& higher,
                              const std::vector<std::string>& lower);

  bool Solve();

  bool SolveWith(const std::vector<ConstraintExpr>& inline_constraints);

  bool Check(const std::vector<ConstraintExpr>& constraints = {});

  int64_t GetValue(std::string_view name) const;

  double GetRealValue(std::string_view name) const;

  void SetRandMode(std::string_view name, bool enabled);
  bool GetRandMode(std::string_view name) const;

  void SetAllRandMode(bool enabled);

  void ApplyInlineRandomList(const std::vector<std::string>& names);

  void SetValue(std::string_view name, int64_t value);

  void SetConstraintMode(std::string_view block_name, bool enabled);
  bool GetConstraintMode(std::string_view block_name) const;

  void SetPreRandomize(RandomizeCallback cb);
  void SetPostRandomize(RandomizeCallback cb);

  const std::unordered_map<std::string, int64_t>& GetValues() const;

 private:
  int64_t GenerateRandValue(RandVariable& var);

  double GenerateRandRealValue(RandVariable& var);

  int64_t DrawDistItem(const DistWeight& item,
                       const std::vector<DistWeight>& weights,
                       int64_t domain_lo, int64_t domain_hi, bool is_signed);

  int64_t SampleDefaultValue(const std::vector<DistWeight>& weights,
                             int64_t domain_lo, int64_t domain_hi,
                             bool is_signed);

  int64_t SampleDist(const ConstraintExpr& c,
                     const std::vector<ConstraintExpr>& extra);

  double DrawRealDistItem(const DistWeight& item,
                          const std::vector<DistWeight>& weights,
                          double domain_lo, double domain_hi);
  double SampleRealDist(const ConstraintExpr& c);

  void SeedDist(const ConstraintExpr& c,
                const std::vector<ConstraintExpr>& extra);

  bool DistValueAdmissible(const std::string& name,
                           const std::vector<ConstraintExpr>& extra) const;

  bool HasEmptyDomain() const;

  bool DistLacksRandVariable() const;

  bool HasRandcInUnique() const;

  bool UniqueMembersNotEquivalentType() const;

  bool ApplyConstraint(const ConstraintExpr& expr);

  bool CheckAllConstraints(const std::vector<ConstraintExpr>& extra,
                           bool include_soft);

  bool SolveBySoftPriority(const std::vector<ConstraintExpr>& extra);
  bool HonoredBoundsConflict(const std::vector<ConstraintExpr>& extra) const;

  void ComputeDisabledSoft(const std::vector<ConstraintExpr>& extra);

  bool DeclaredSigned(const std::string& name) const;

  bool EvalConstraint(const ConstraintExpr& expr) const;

  int64_t FoldReduction(const ConstraintExpr& expr) const;

  bool EvalImplication(const ConstraintExpr& expr) const;

  bool EvalIfElse(const ConstraintExpr& expr) const;

  bool EvalForeach(const ConstraintExpr& expr) const;

  bool EvalArrayReduction(const ConstraintExpr& expr) const;

  bool EvalUnique(const ConstraintExpr& expr) const;

  void RefreshStaticBlockState();

  void ApplyDistConstraints(const std::vector<ConstraintExpr>& extra);

  void ApplyDirectConstraints(const std::vector<ConstraintExpr>& extra,
                              bool include_soft);

  std::unordered_map<std::string, int64_t> DrawArraySizesOnce(
      const std::vector<ConstraintExpr>& extra, bool include_soft,
      const std::function<int64_t(RandVariable&)>& gen);
  bool SizeConstraintsHold(const std::vector<ConstraintExpr>& extra);
  void HoldArraySizes(const std::unordered_map<std::string, int64_t>& sizes);

  bool SoftSeedApplies(const ConstraintExpr& c, bool include_soft) const;

  void SeedSoftBounds(const std::vector<ConstraintExpr>& extra,
                      bool include_soft);
  void SeedHonoredSoft(const ConstraintExpr& inner,
                       const std::vector<ConstraintExpr>& extra);

  bool HoldsStateValue(std::string_view name) const;

  bool SolveIterative(const std::vector<ConstraintExpr>& extra,
                      bool include_soft);
  bool RandcValueAdmissible(const std::string& name,
                            const std::vector<ConstraintExpr>& extra) const;
  std::function<int64_t(RandVariable&)> RandcOncePerSolve(
      std::unordered_map<std::string, int64_t>& drawn,
      const std::vector<ConstraintExpr>& extra);
  bool DrawAdmissibleRandc(RandVariable& var,
                           const std::vector<ConstraintExpr>& extra,
                           int64_t& out);
  bool OwnAdmissibleValues(const RandVariable& var,
                           const std::vector<ConstraintExpr>& extra,
                           bool need_custom, std::vector<int64_t>& out);
  bool ConstrainsAlone(const ConstraintExpr& c, const std::string& name) const;
  std::vector<int64_t> AdmittedValues(
      const std::string& name, const std::vector<const ConstraintExpr*>& own,
      const std::vector<int64_t>& domain);
  void SeedEnumerableVariables(
      const std::vector<ConstraintExpr>& extra,
      std::unordered_map<std::string, std::vector<int64_t>>& enumerated);
  void PruneRefusedRandcValues(std::unordered_map<std::string, int64_t>& drawn,
                               const std::vector<ConstraintExpr>& extra) const;

  void RepairConstraints(const std::vector<ConstraintExpr>& extra);
  void RepairConstraint(const ConstraintExpr& c);
  void RepairConsequent(const ConstraintExpr& sub);
  void RepairReduction(const ConstraintExpr& c);
  bool RepairReductionElement(const ConstraintExpr& c, const std::string& name);
  int64_t ReductionDistanceWith(const ConstraintExpr& c,
                                const std::string& name, int64_t candidate);
  void ApplyCustomRepair(const ConstraintExpr& c);
  void ApplyDerived(const ConstraintExpr& c);
  void NarrowAtValues(const ConstraintExpr& c, const std::string& name,
                      RandVariable& dom, std::vector<int64_t>& members,
                      bool& has_members) const;
  void NarrowBoundAtValues(const ConstraintExpr& c, const std::string& name,
                           RandVariable& dom) const;
  void NarrowByActive(const std::string& name, RandVariable& dom,
                      std::vector<int64_t>& members, bool& has_members) const;
  void SeedAttempt(const std::vector<ConstraintExpr>& extra, bool include_soft,
                   bool repair,
                   const std::unordered_map<std::string, int64_t>& sizes,
                   const std::function<int64_t(RandVariable&)>& gen_randc);
  bool FlatPass(const std::vector<ConstraintExpr>& extra, bool include_soft,
                bool repair, const std::function<int64_t(RandVariable&)>& gen,
                const std::function<double(RandVariable&)>& gen_real);
  bool AntecedentHolds(const ConstraintExpr& c) const;
  bool SoftHonored(const ConstraintExpr& c) const;
  void DrawPropagated(const std::vector<ConstraintExpr>& extra);
  void RepairFromCandidates(const ConstraintExpr& c);
  bool RepairMayWrite(const std::string& name) const;
  void RepairWithin(const std::vector<std::string>& names,
                    const std::vector<ConstraintExpr>& extra);
  void RepairReadyWithin(const std::vector<std::string>& names,
                         const std::unordered_set<std::string>& committed,
                         const std::vector<ConstraintExpr>& extra);
  bool DrawPriorityLayer(const std::vector<std::string>& layer,
                         const std::unordered_set<std::string>& committed,
                         const std::vector<ConstraintExpr>& extra,
                         bool include_soft);

  void CommitStaticSharedValues();

  std::vector<std::vector<std::string>> ComputeSolveGroups(
      const std::vector<std::string>& vars) const;

  bool SolveOrderedGroups(const std::vector<std::vector<std::string>>& groups,
                          size_t idx, const std::vector<ConstraintExpr>& extra,
                          bool include_soft);

  bool HasFunctionArgPriorityCycle() const;

  std::vector<std::vector<std::string>> ComputePriorityLayers(
      const std::vector<std::string>& vars) const;

  bool SolvePriorityLayers(const std::vector<std::vector<std::string>>& layers,
                           const std::vector<ConstraintExpr>& extra,
                           bool include_soft);

  bool CheckCommittedConstraints(
      const std::vector<ConstraintExpr>& extra, bool include_soft,
      const std::unordered_set<std::string>& committed) const;

  std::mt19937 rng_;
  std::string name_scope_;
  std::unordered_map<std::string, RandVariable> variables_;
  std::vector<ConstraintBlock> blocks_;
  std::unordered_map<std::string, int64_t> values_;
  std::unordered_map<std::string, double> real_values_;
  RandomizeCallback pre_randomize_;
  RandomizeCallback post_randomize_;

  std::vector<std::pair<std::string, std::string>> solve_before_edges_;

  std::vector<std::pair<std::string, std::string>> function_arg_priority_edges_;

  bool guard_error_ = false;

  std::unordered_set<std::string> repair_scope_;
  const std::vector<ConstraintExpr>* repair_extra_ = nullptr;

  std::unordered_set<const ConstraintExpr*> dropped_soft_;
  std::unordered_map<std::string, std::vector<int64_t>> enumerated_;

  std::unordered_set<const ConstraintExpr*> disabled_soft_;
};

}  // namespace delta
