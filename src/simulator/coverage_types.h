#ifndef DELTA_SIMULATOR_COVERAGE_TYPES_H_
#define DELTA_SIMULATOR_COVERAGE_TYPES_H_

#include <cstdint>
#include <string>
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
  // Per-bin guard from a trailing "iff" on a value bin definition: when the
  // guard expression is false at a sampling point, the bin's count is not
  // incremented (LRM 19.5.1).
  bool has_iff_guard = false;
  bool iff_guard_value = true;
};

// One partition of a real coverpoint range. A real bin may divide a range of
// real values into intervals; each interval includes its low value and excludes
// its high value, except the final interval of a range, which also includes its
// high value (LRM 19.5.1).
struct RealInterval {
  double low = 0.0;
  double high = 0.0;
  bool high_inclusive = false;
};

// Effective type of a coverpoint expression e, used when resolving bin values
// against e (LRM 19.5.7). It is `width` bits wide and interpreted in
// two's-complement when `is_signed`. A bin value is reconciled to this type
// before it is compared with a sampled value: with an explicit coverpoint cast
// type the effective type is that type, otherwise it is the self-determined
// type of e (LRM 19.5.7 a).
struct CoverpointEffectiveType {
  uint32_t width = 32;
  bool is_signed = true;
};

// Outcome of resolving a single bin value b against the effective type of e
// (LRM 19.5.7 b). Any result other than kOk causes an implementation warning,
// and the value is then dropped from the bin by the warning rules of LRM
// 19.5.7.
enum class BinValueResolution : uint8_t {
  // b is representable in the effective type and participates in the bin.
  kOk,
  // The effective type is unsigned but b is signed and negative (LRM
  // 19.5.7 b, condition 1).
  kUnsignedNegative,
  // Statically casting b to the effective type yields a different value (LRM
  // 19.5.7 b, condition 2).
  kValueChanged,
  // b carries x or z bits and the bin is not a wildcard bin (LRM 19.5.7 b,
  // condition 3).
  kUnknownBits,
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
  std::vector<int64_t> sample_history = {};
  // Weight Wi of this coverpoint within the covergroup coverage average (LRM
  // 19.11). The value originates from option.weight (LRM 19.7); a coverpoint
  // carries it so the covergroup average can weight each item.
  int32_t weight = 1;
  // When the coverpoint's own coverage rules (LRM 19.11.1) indicate it is to be
  // excluded, the covergroup average drops it from both the numerator and the
  // denominator (LRM 19.11).
  bool excluded_from_coverage = false;
  // Number of run-time errors raised by samples that hit an illegal bin. An
  // illegal value or transition occurrence is reported as a run-time error and
  // contributes to no coverage bin; illegal bins take precedence over every
  // other bin a sample might also match (LRM 19.5.6).
  uint64_t illegal_violations = 0;
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
  // When the cross's own coverage rules (LRM 19.11.2) indicate it is to be
  // excluded, the covergroup average drops it from both the numerator and the
  // denominator (LRM 19.11).
  bool excluded_from_coverage = false;
};

// The matches selection policy of a select_expression "with" clause: the
// minimum number of a candidate bin tuple's value tuples that must satisfy the
// with_covergroup_expression for the bin tuple to be selected. require_all
// models the $ token, which requires every value tuple to satisfy; otherwise at
// least min_count must, which defaults to one when no matches clause is written
// (LRM 19.6.1.2).
struct CrossWithMatchPolicy {
  bool require_all = false;
  uint64_t min_count = 1;
};

// Instance options of a covergroup, as organized in LRM 19.10. The numeric
// members are the signed integers the standard prescribes (int weight, int
// goal, int at_least, int auto_bin_max), matching the sibling coverpoint and
// cross option structures below.
struct CoverOptions {
  int32_t at_least = 1;
  int32_t weight = 1;
  int32_t goal = 100;
  int32_t auto_bin_max = 64;
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
  CoverGroupTypeOption type_option = {};
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
// Table 19-4). The same levels apply to instance options (LRM 19.7, Table
// 19-2).
enum class CoverSyntacticLevel : uint8_t {
  kCovergroup,
  kCoverpoint,
  kCross,
};

// Identifies an instance-specific coverage option for the Table 19-1/Table
// 19-2 queries (LRM 19.7).
enum class InstanceOptionKind : uint8_t {
  kName,
  kWeight,
  kGoal,
  kComment,
  kAtLeast,
  kAutoBinMax,
  kCrossNumPrintMissing,
  kCrossRetainAutoBins,
  kDetectOverlap,
  kPerInstance,
  kGetInstCoverage,
};

// The repetition a transition item may carry inside a transition bin (LRM
// 19.5.2). Consecutive repetition repeats a value at successive sample points;
// the goto and nonconsecutive forms permit intervening samples and mirror the
// assertion repetitions of §16.9.2.
enum class TransitionRepeatKind : uint8_t {
  kConsecutive,     // trans_item [* repeat_range]
  kGoto,            // trans_item [-> repeat_range]
  kNonconsecutive,  // trans_item [= repeat_range]
};

// How a sampled cross product is treated once a cross's illegal_bins and
// ignore_bins select expressions have been evaluated to their product sets
// (LRM 19.6.3). A counted product contributes to its cross coverage bin; an
// ignored product is excluded from coverage with no diagnostic; an illegal
// product is excluded from coverage and raises a run-time error.
enum class CrossSampleOutcome : uint8_t {
  kCounted,
  kIgnored,
  kIllegalError,
};

}  // namespace delta

#endif  // DELTA_SIMULATOR_COVERAGE_TYPES_H_
