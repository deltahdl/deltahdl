#pragma once

#include <cstdint>
#include <deque>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

namespace delta {

enum class CoverBinKind : uint8_t {
  kExplicit,
  kAuto,
  kTransition,
  kWildcard,
  kIllegal,
  kIgnore,
  // A default bin catches every sampled value that does not fall within any
  // other defined bin of its coverpoint (see LRM 19.5).
  kDefault,
};

struct CoverBin {
  std::string name;
  CoverBinKind kind = CoverBinKind::kExplicit;
  std::vector<int64_t> values;
  std::vector<std::vector<int64_t>> transitions;
  uint64_t hit_count = 0;
  uint32_t at_least = 1;
};

struct CoverPoint {
  std::string name;
  std::vector<CoverBin> bins;
  bool has_iff_guard = false;
  bool iff_guard_value = true;
  int64_t auto_bin_min = 0;
  int64_t auto_bin_max = 0;
  uint32_t auto_bin_count = 64;
  // True when the coverpoint expression is of a real type. A real coverpoint
  // cannot accept a "with" bin filter (LRM 19.5.1.1) and cannot be crossed as
  // a bare variable (LRM 19.6).
  bool is_real = false;
  // Trailing window of recently sampled values, used to recognize value
  // transition sequences for transition bins.
  std::vector<int64_t> sample_history;
};

struct CrossBin {
  std::string name;
  std::vector<std::vector<int64_t>> value_sets;
  uint64_t hit_count = 0;
  uint32_t at_least = 1;
  // Per-bin guard from a trailing "iff" on a cross bin definition: when the
  // guard expression is false at a sampling point the bin is not counted
  // (LRM 19.6).
  bool has_iff_guard = false;
  bool iff_guard_value = true;
};

// Static (type) options of a cross, as organized in LRM 19.10. Type options
// describe a property of the covergroup type as a whole (LRM 19.7.1).
struct CrossTypeOption {
  int32_t weight = 1;
  int32_t goal = 100;
  std::string comment;
};

// Instance options of a cross, as organized in LRM 19.10.
struct CrossOption {
  int32_t weight = 1;
  int32_t goal = 100;
  std::string comment;
  int32_t at_least = 1;
  int32_t cross_num_print_missing = 0;
  bool cross_retain_auto_bins = true;
};

struct CrossCover {
  std::string name;
  std::vector<std::string> coverpoint_names;
  std::vector<CrossBin> bins;
  // Guard from an "iff" on the cross declaration: when false at a sampling
  // point the whole cross is ignored (LRM 19.6).
  bool has_iff_guard = false;
  bool iff_guard_value = true;
  CrossOption option;
  CrossTypeOption type_option;
};

// Instance options of a covergroup, as organized in LRM 19.10. The legacy
// fields (at_least, weight, goal, auto_bin_max) are kept so existing coverage
// computations continue to work unchanged.
struct CoverOptions {
  uint32_t at_least = 1;
  uint32_t weight = 1;
  double goal = 100.0;
  uint32_t auto_bin_max = 64;
  std::string name;
  std::string comment;
  int32_t cross_num_print_missing = 0;
  bool cross_retain_auto_bins = true;
  bool detect_overlap = false;
  bool per_instance = false;
  bool get_inst_coverage = false;
};

// Instance options of a coverpoint, as organized in LRM 19.10.
struct CoverPointOption {
  int32_t weight = 1;
  int32_t goal = 100;
  std::string comment;
  int32_t at_least = 1;
  int32_t auto_bin_max = 64;
  bool detect_overlap = false;
};

// Static (type) options of a coverpoint, as organized in LRM 19.10.
struct CoverPointTypeOption {
  int32_t weight = 1;
  int32_t goal = 100;
  std::string comment;
  double real_interval = 1.0;
};

// Static (type) options of a covergroup, as organized in LRM 19.10. Their
// defaults and meaning are defined in LRM 19.7.1 (Table 19-3).
struct CoverGroupTypeOption {
  int32_t weight = 1;
  int32_t goal = 100;
  std::string comment;
  bool strobe = false;
  bool merge_instances = false;
  bool distribute_first = false;
  double real_interval = 1.0;
};

struct CoverGroup {
  std::string name;
  std::vector<CoverPoint> coverpoints;
  std::vector<CrossCover> crosses;
  CoverOptions options;
  uint64_t sample_count = 0;
  // Whether the instance is currently collecting coverage. start() and stop()
  // toggle this; while stopped a triggered sample() records nothing (LRM 19.8).
  bool collecting = true;
  CoverGroupTypeOption type_option;
};

// Identifies a covergroup type option for the Table 19-4 placement queries
// (LRM 19.7.1).
enum class TypeOptionKind : uint8_t {
  kWeight,
  kGoal,
  kComment,
  kStrobe,
  kMergeInstances,
  kDistributeFirst,
  kRealInterval,
};

// The syntactic level at which an option assignment appears (LRM 19.7.1,
// Table 19-4).
enum class CoverSyntacticLevel : uint8_t {
  kCovergroup,
  kCoverpoint,
  kCross,
};

class CoverageDB {
 public:
  CoverGroup* CreateGroup(std::string name);
  CoverGroup* FindGroup(std::string_view name);
  uint32_t GroupCount() const;

  static CoverPoint* AddCoverPoint(CoverGroup* group, std::string name);
  static CoverBin* AddBin(CoverPoint* cp, CoverBin bin);

  static void AutoCreateBins(CoverPoint* cp, int64_t min_val, int64_t max_val);

  static CrossCover* AddCross(CoverGroup* group, CrossCover cross);

  void Sample(CoverGroup* group,
              const std::vector<std::pair<std::string, int64_t>>& values);

  static double GetCoverage(const CoverGroup* group);
  static double GetInstCoverage(const CoverGroup* group);
  static double GetPointCoverage(const CoverPoint* cp);
  static double GetCrossCoverage(const CrossCover* cross);

  double GetGlobalCoverage() const;

  // --- LRM 19.8: predefined coverage methods --------------------------------

  // start()/stop() control whether the instance collects coverage. While
  // stopped, a triggered sample() records neither a sampling event nor any bin
  // hit (LRM 19.8).
  static void Start(CoverGroup* group);
  static void Stop(CoverGroup* group);

  // set_inst_name() assigns the instance name procedurally (LRM 19.8). The
  // instance name is the per-instance option.name of LRM 19.10.
  static void SetInstName(CoverGroup* group, std::string name);

  // The optional ref-int pair of get_coverage()/get_inst_coverage() reports the
  // number of covered bins and the number of coverage bins defined for the
  // item. For a covergroup the counts are aggregated over all coverpoints and
  // crosses; for a coverpoint or cross they are the numerator and denominator
  // of the (unscaled) coverage value (LRM 19.8).
  static double GetCoverage(const CoverGroup* group, int32_t& covered_bins,
                            int32_t& total_bins);
  static double GetInstCoverage(const CoverGroup* group, int32_t& covered_bins,
                                int32_t& total_bins);

  // --- LRM 19.6: cross coverage ---------------------------------------------

  // Ensures a coverpoint exists for every name listed in a cross. When a bare
  // variable is crossed, an implicit coverpoint is created for it as though it
  // had been declared with "coverpoint <var>;" (LRM 19.6).
  static void EnsureCrossCoverPoints(CoverGroup* group,
                                     const std::vector<std::string>& names);

  // True when every cross item resolves to a coverpoint defined in the same
  // covergroup. Crossing items from another covergroup is illegal (LRM 19.6).
  static bool CrossItemsInSameGroup(const CoverGroup* group,
                                    const std::vector<std::string>& names);

  // Builds the cross bins as the Cartesian product of the constituent
  // coverpoints' bins. Default, ignore, and illegal coverpoint bins do not
  // contribute any cross product (LRM 19.6).
  static void AutoCreateCrossBins(CoverGroup* group, CrossCover* cross);

  // A bare variable crossed directly must be integral. A real value can only
  // participate in a cross through an explicitly declared coverpoint of a real
  // expression (LRM 19.6).
  static bool CrossBareVariableAllowed(bool variable_is_real);

  // --- LRM 19.5.1.1: coverpoint bin "with" expressions ----------------------

  // Selects the candidate values for which the per-value predicate is true.
  // The predicate receives each candidate (the "item" of the with expression).
  // Order and duplicate values are preserved (LRM 19.5.1.1).
  static std::vector<int64_t> ApplyWithExpression(
      const std::vector<int64_t>& candidates,
      const std::function<bool(int64_t)>& pred);

  // Applies a with expression and distributes the values into num_bins bins.
  // By default the filter runs before distribution; distribute_first (a
  // covergroup type option, LRM 19.7.1) runs distribution first and filters the
  // contents of each resulting bin (LRM 19.5.1.1).
  static std::vector<std::vector<int64_t>> ApplyWithAndDistribute(
      const std::vector<int64_t>& candidates,
      const std::function<bool(int64_t)>& pred, uint32_t num_bins,
      bool distribute_first);

  // A with bin filter is illegal on a coverpoint of a real type (LRM 19.5.1.1).
  static bool WithExpressionAllowed(const CoverPoint* cp);

  // In place of an explicit range list, a with expression may name the
  // enclosing coverpoint to denote all of its values; no other coverpoint name
  // is permitted (LRM 19.5.1.1).
  static bool WithRangeReferenceAllowed(std::string_view self_name,
                                        std::string_view referenced_name);

  // --- LRM 19.7.1: covergroup type options ----------------------------------

  // Computes type (cumulative) coverage over the instances of a covergroup
  // type. With merge_instances the bins are unioned across instances (a bin is
  // covered if any instance covered it); otherwise the per-instance coverage is
  // combined as a weighted average (LRM 19.7.1).
  static double ComputeTypeCoverage(
      const std::vector<const CoverGroup*>& instances, bool merge_instances);

  // Table 19-4: whether a type option may be assigned at a given syntactic
  // level (LRM 19.7.1).
  static bool TypeOptionAllowedAt(TypeOptionKind kind,
                                  CoverSyntacticLevel level);

  // When set at the covergroup level, only real_interval acts as a default for
  // lower syntactic levels (LRM 19.7.1).
  static bool TypeOptionDefaultsToLowerLevels(TypeOptionKind kind);

  // strobe and real_interval may only be set in the covergroup definition; the
  // remaining type options may also be assigned procedurally (LRM 19.7.1).
  static bool TypeOptionSettableProcedurally(TypeOptionKind kind);

 private:
  void SampleCoverPoint(CoverPoint* cp, int64_t value);
  void SampleCross(CrossCover* cross,
                   const std::vector<std::pair<std::string, int64_t>>& vals);

  std::deque<CoverGroup> groups_;
  std::unordered_map<std::string, size_t> name_index_;
};

}
