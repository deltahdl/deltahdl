#pragma once

#include <cstddef>
#include <cstdint>
#include <deque>
#include <functional>
#include <iosfwd>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "simulator/coverage_types.h"

namespace delta {

class CoverageDB {
 public:
  CoverGroup* CreateGroup(std::string name);
  CoverGroup* FindGroup(std::string_view name);
  uint32_t GroupCount() const;

  static CoverPoint* AddCoverPoint(CoverGroup* group, std::string name);
  static CoverBin* AddBin(CoverPoint* cp, CoverBin bin);

  static void AutoCreateBins(CoverPoint* cp, int64_t min_val, int64_t max_val);
  static void AutoCreateEnumBins(
      CoverPoint* cp,
      const std::vector<std::pair<std::string_view, int64_t>>& members);

  static CrossCover* AddCross(CoverGroup* group, CrossCover cross);

  void Sample(CoverGroup* group,
              const std::vector<std::pair<std::string, int64_t>>& values);
  void Sample(CoverGroup* group,
              const std::vector<std::pair<std::string, int64_t>>& values,
              const std::vector<std::pair<std::string, double>>& real_values);

  static double GetCoverage(const CoverGroup* group);
  static double GetInstCoverage(const CoverGroup* group);
  static double GetPointCoverage(const CoverPoint* cp);
  static double GetCrossCoverage(const CrossCover* cross);

  double GetGlobalCoverage() const;

  void SetCoverageDbName(std::string filename);
  const std::string& CoverageDbName() const;

  void MergeCumulativeCoverage(const std::vector<CoverGroup>& cumulative);

  bool LoadCoverageDbFile(const std::string& path);

  void SaveCoverageDbFile(const std::string& path) const;
  void SaveNamedCoverageDb() const;

  const CoverGroup* LoadedCoverageOf(std::string_view type_name) const;

  static void AddCumulativeCounts(CoverGroup& group,
                                  const CoverGroup& cumulative);

  void ReportMissingCrossBins(std::ostream& os) const;

  static void Start(CoverGroup* group);
  static void Stop(CoverGroup* group);

  static void SetInstName(CoverGroup* group, std::string name);

  static double GetCoverage(const CoverGroup* group, int32_t& covered_bins,
                            int32_t& total_bins);
  static double GetInstCoverage(const CoverGroup* group, int32_t& covered_bins,
                                int32_t& total_bins);

  static void EnsureCrossCoverPoints(CoverGroup* group,
                                     const std::vector<std::string>& names);

  static bool CrossItemsInSameGroup(const CoverGroup* group,
                                    const std::vector<std::string>& names);

  static void AutoCreateCrossBins(CoverGroup* group, CrossCover* cross);
  static std::vector<std::vector<size_t>> CrossProductTuples(
      const CoverGroup* group, const CrossCover* cross);
  static std::string CrossProductName(const CoverGroup* group,
                                      const CrossCover* cross,
                                      const std::vector<size_t>& tuple);
  static bool CrossTupleSampled(const CoverGroup* group,
                                const CrossCover* cross,
                                const std::vector<size_t>& tuple);

  static bool CrossBareVariableAllowed(bool variable_is_real);

  static std::vector<std::vector<int64_t>> BinsofYield(const CoverPoint* cp,
                                                       int64_t bin_index = -1);

  static std::vector<size_t> SelectBinsByIntersect(
      const std::vector<std::vector<int64_t>>& bins,
      const std::vector<int64_t>& values, bool negate);

  static std::vector<std::vector<size_t>> EnumerateCrossProducts(
      const std::vector<size_t>& per_point_bin_counts);

  static std::vector<std::vector<size_t>> SelectProductsByPointBins(
      const std::vector<size_t>& per_point_bin_counts, size_t point,
      const std::vector<size_t>& selected_point_bins);

  static std::vector<std::vector<size_t>> AndCrossSelections(
      const std::vector<std::vector<size_t>>& lhs,
      const std::vector<std::vector<size_t>>& rhs);

  static std::vector<std::vector<size_t>> OrCrossSelections(
      const std::vector<std::vector<size_t>>& lhs,
      const std::vector<std::vector<size_t>>& rhs);

  static std::vector<std::vector<size_t>> RetainedAutoCrossProducts(
      const std::vector<size_t>& per_point_bin_counts,
      const std::vector<std::vector<size_t>>& user_selected_products,
      bool retain_auto_bins);

  static std::vector<int64_t> BinsofBinValues(const CoverBin& bin);

  static uint64_t CountSatisfyingValueTuples(
      const std::vector<std::vector<int64_t>>& bin_tuple_value_sets,
      const std::function<bool(const std::vector<int64_t>&)>& pred);

  static std::vector<size_t> SelectCrossBinTuples(
      const std::vector<std::vector<std::vector<int64_t>>>&
          candidate_bin_tuples,
      const std::function<bool(const std::vector<int64_t>&)>* pred,
      const CrossWithMatchPolicy& policy);

  static std::vector<size_t> SelectCrossBinTuplesBySetExpression(
      const std::vector<std::vector<std::vector<int64_t>>>&
          candidate_bin_tuples,
      const std::vector<std::vector<int64_t>>& set_expression_elements,
      const CrossWithMatchPolicy& policy);

  static std::vector<std::vector<size_t>> ExcludeIgnoredCrossProducts(
      const std::vector<std::vector<size_t>>& products,
      const std::vector<std::vector<size_t>>& ignored);

  static bool IgnoredCrossProductRetained(bool also_in_other_cross_bin);

  static std::vector<std::vector<size_t>> ExcludeIllegalCrossProducts(
      const std::vector<std::vector<size_t>>& products,
      const std::vector<std::vector<size_t>>& illegal);

  static CrossSampleOutcome ClassifyCrossSample(
      const std::vector<size_t>& product,
      const std::vector<std::vector<size_t>>& illegal,
      const std::vector<std::vector<size_t>>& ignored,
      bool also_in_other_cross_bin);

  static std::vector<std::vector<int64_t>> DistributeValues(
      const std::vector<int64_t>& values, uint32_t num_bins);

  static std::string StateBinName(std::string_view base, int64_t index);

  static std::vector<CoverBin> OpenArrayValueBins(
      std::string_view base, const std::vector<int64_t>& values);

  static std::vector<RealInterval> RealRangeIntervals(double low, double high,
                                                      double interval,
                                                      bool uses_dollar);

  static std::string RealIntervalBinName(std::string_view base,
                                         const RealInterval& interval);

  static std::string RealValueBinName(std::string_view base, double value);

  static std::vector<RealInterval> MergeIdenticalIntervals(
      const std::vector<RealInterval>& intervals);

  static bool RealDefaultBinMayBeArray();

  static std::pair<double, double> ToleranceRange(double value,
                                                  double tolerance,
                                                  bool is_percent);

  static std::vector<int64_t> ApplyWithExpression(
      const std::vector<int64_t>& candidates,
      const std::function<bool(int64_t)>& pred);

  static std::vector<std::vector<int64_t>> ApplyWithAndDistribute(
      const std::vector<int64_t>& candidates,
      const std::function<bool(int64_t)>& pred, uint32_t num_bins,
      bool distribute_first);

  static bool WithExpressionAllowed(const CoverPoint* cp);

  static bool WithRangeReferenceAllowed(std::string_view self_name,
                                        std::string_view referenced_name);

  static uint64_t SetExpressionEvaluationCount(uint64_t sample_count);

  static bool TransitionBinAllowed(const CoverPoint* cp);

  static bool TransitionLengthLegal(size_t sample_points);

  static std::vector<std::vector<int64_t>> ExpandSetTransition(
      const std::vector<std::vector<int64_t>>& steps);

  static std::vector<std::vector<int64_t>> ExpandConsecutiveRepeat(
      const std::vector<int64_t>& item, uint32_t lo, uint32_t hi);

  static std::string TransitionArrayBinName(
      std::string_view base, const std::vector<int64_t>& transition);

  static bool TransitionRepeatBounded(TransitionRepeatKind kind);

  static bool MultipleBinsAllowsTransition(bool sequence_bounded);

  static bool DefaultSequenceAllowsMultipleBins();

  static bool DefaultSequenceTransitionIncrements(
      bool any_nondefault_incremented, bool any_pending);

  static bool AutoBinsAllowed(const CoverPoint* cp);

  static bool ShouldAutoCreateBins(const CoverPoint* cp);

  static uint64_t AutoBinCount(uint32_t coverpoint_bits, uint64_t auto_bin_max);

  static uint64_t AutoBinCountEnum(uint64_t enum_cardinality);

  static bool AutoBinSampleIncluded(bool sample_has_xz);

  static std::string AutoBinName(int64_t low, int64_t high);

  static std::string AutoEnumBinName(std::string_view constant_name);

  static std::vector<int64_t> ExpandWildcardValue(int64_t pattern,
                                                  uint64_t care_mask,
                                                  uint32_t width);

  static bool WildcardSampleIncluded(bool sample_has_xz);

  static bool WildcardBinsAllowed(const CoverPoint* cp);

  static std::vector<int64_t> RemoveIgnoredValues(
      const std::vector<int64_t>& bin_values,
      const std::vector<int64_t>& ignored_values);

  static bool CoveredTransitionIsIgnored(const std::vector<int64_t>& covered,
                                         const std::vector<int64_t>& ignored);

  static bool IgnoredValueAffectsTransition(
      int64_t ignored_value, const std::vector<int64_t>& transition);

  static bool IgnoreTransitionLengthLegal(bool sequence_bounded);

  static std::vector<int64_t> RemoveIllegalValues(
      const std::vector<int64_t>& bin_values,
      const std::vector<int64_t>& illegal_values);

  static bool CoveredTransitionIsIllegal(const std::vector<int64_t>& covered,
                                         const std::vector<int64_t>& illegal);

  static bool IllegalValueAffectsTransition(
      int64_t illegal_value, const std::vector<int64_t>& transition);

  static bool IllegalTransitionLengthLegal(bool sequence_bounded);

  static bool IllegalTakesPrecedence(bool also_in_other_bin);

  static CoverpointEffectiveType EffectiveCoverpointType(
      bool has_coverpoint_type, CoverpointEffectiveType coverpoint_type,
      CoverpointEffectiveType self_determined_type);

  static int64_t CastToEffectiveType(int64_t value,
                                     CoverpointEffectiveType eff);

  static int64_t EffectiveTypeMin(CoverpointEffectiveType eff);
  static int64_t EffectiveTypeMax(CoverpointEffectiveType eff);

  static BinValueResolution ResolveBinValue(int64_t value, bool value_is_signed,
                                            bool value_has_xz, bool is_wildcard,
                                            CoverpointEffectiveType eff);

  static bool SingletonValueParticipates(BinValueResolution resolution);

  struct BinRangeSpec {
    int64_t low = 0;
    int64_t high = 0;
    bool low_has_xz = false;
    bool high_has_xz = false;
    bool is_wildcard = false;
  };

  static std::vector<int64_t> ResolveBinRange(const BinRangeSpec& range,
                                              CoverpointEffectiveType eff);

  static bool OptionWeightValid(int32_t weight);

  static bool OptionSpecifiedMoreThanOnce(
      const std::vector<InstanceOptionKind>& assigned);

  static bool OptionAllowedAt(InstanceOptionKind kind,
                              CoverSyntacticLevel level);

  static bool OptionDefaultsToLowerLevels(InstanceOptionKind kind);

  static bool OptionSettableProcedurally(InstanceOptionKind kind);

  static double ComputeTypeCoverage(
      const std::vector<const CoverGroup*>& instances, bool merge_instances);

  static bool TypeOptionAllowedAt(TypeOptionKind kind,
                                  CoverSyntacticLevel level);

  static bool TypeOptionDefaultsToLowerLevels(TypeOptionKind kind);

  static bool TypeOptionSettableProcedurally(TypeOptionKind kind);

  static bool CovergroupCoverageDenominatorZero(const CoverGroup* group);

  static double ComputeOverallCoverage(
      const std::vector<const CoverGroup*>& instances);

  static bool PointCoverageDenominatorZero(const CoverPoint* cp);

  static double GetPointCoverage(const CoverPoint* cp, int32_t& covered_bins,
                                 int32_t& total_bins);

  static uint32_t CumulativeAtLeast(
      const std::vector<uint32_t>& at_least_values);

  static uint64_t CrossAutoBinCount(
      const std::vector<uint64_t>& per_point_bin_counts,
      uint64_t user_defined_cross_products);

  static uint64_t CrossCoverageDenominator(
      const std::vector<uint64_t>& per_point_bin_counts,
      uint64_t user_defined_cross_products, uint64_t significant_user_bins);

  static bool CrossBinCountsTowardCoverage(CrossSampleOutcome outcome);

  static bool CrossCoverageDenominatorZero(const CrossCover* cross);

  static double GetCrossCoverage(const CrossCover* cross, int32_t& covered_bins,
                                 int32_t& total_bins);

  static double ComputePointTypeCoverage(
      const std::vector<const CoverPoint*>& instances, bool merge_instances);

  static double ComputeCrossTypeCoverage(
      const std::vector<const CrossCover*>& instances, bool merge_instances);

  static void ApplyDerivedCoverpointOverrides(
      CoverGroup* base,
      const std::vector<std::string>& derived_coverpoint_names);

  static void ApplyDerivedCrossOverrides(
      CoverGroup* base, const std::vector<std::string>& derived_cross_names);

  static bool CovergroupTypesAggregate(std::string_view type_a,
                                       std::string_view type_b);

 private:
  void SampleCoverPoint(CoverPoint* cp, int64_t value);
  void SampleRealCoverPoint(CoverPoint* cp, double value);
  void SampleCross(CrossCover* cross,
                   const std::vector<std::pair<std::string, int64_t>>& vals);

  std::deque<CoverGroup> groups_;
  std::unordered_map<std::string, size_t> name_index_;
  std::deque<CoverGroup> loaded_;
  std::string coverage_db_name_;
};

}  // namespace delta
