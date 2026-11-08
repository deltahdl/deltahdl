#ifndef DELTA_SIMULATOR_COVERAGE_TYPES_H_
#define DELTA_SIMULATOR_COVERAGE_TYPES_H_

#include <cstddef>
#include <cstdint>
#include <deque>
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
  kDefault,
  kDefaultSequence,
};

enum class TransitionRepeatKind : uint8_t {
  kConsecutive,
  kGoto,
  kNonconsecutive,
};

struct TransitionPatternElement {
  std::vector<int64_t> values;
  bool has_repeat = false;
  TransitionRepeatKind repeat_kind = TransitionRepeatKind::kConsecutive;
  uint32_t repeat_lo = 1;
  uint32_t repeat_hi = 1;
};

struct TransitionMatchThread {
  uint32_t elem = 0;
  uint32_t reps = 0;
  bool gap_ok = false;
};

struct CoverValueRange {
  int64_t lo = 0;
  int64_t hi = 0;
  bool operator==(const CoverValueRange&) const = default;
};

struct RealInterval {
  double low = 0.0;
  double high = 0.0;
  bool high_inclusive = false;
};

struct CoverBin {
  std::string name;
  CoverBinKind kind = CoverBinKind::kExplicit;
  std::vector<int64_t> values;
  std::vector<CoverValueRange> ranges;
  std::vector<RealInterval> real_intervals;
  std::vector<std::vector<int64_t>> transitions;
  std::vector<std::vector<TransitionPatternElement>> transition_patterns;
  std::vector<std::vector<TransitionMatchThread>> pattern_threads;
  uint64_t hit_count = 0;
  uint32_t at_least = 1;
  bool has_iff_guard = false;
  bool iff_guard_value = true;
};

struct CoverpointEffectiveType {
  uint32_t width = 32;
  bool is_signed = true;
};

enum class BinValueResolution : uint8_t {
  kOk,
  kUnsignedNegative,
  kValueChanged,
  kUnknownBits,
};

struct CoverPoint {
  std::string name;
  std::deque<CoverBin> bins;
  bool collecting = true;
  bool has_iff_guard = false;
  bool iff_guard_value = true;
  int64_t auto_bin_min = 0;
  int64_t auto_bin_max = 0;
  uint32_t auto_bin_count = 64;
  bool is_real = false;
  std::vector<int64_t> sample_history = {};
  int32_t weight = 1;
  int32_t type_weight = 1;
  bool excluded_from_coverage = false;
  uint64_t illegal_violations = 0;
  std::vector<size_t> sampled_bins;
  bool sample_has_xz = false;
  bool sampled = false;
};

struct CrossBin {
  std::string name;
  std::vector<std::vector<int64_t>> value_sets;
  std::vector<std::vector<size_t>> bin_tuples;
  uint64_t hit_count = 0;
  uint32_t at_least = 1;
  bool has_iff_guard = false;
  bool iff_guard_value = true;
};

struct CrossTypeOption {
  int32_t weight = 1;
  int32_t goal = 100;
  std::string comment;
};

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
  bool collecting = true;
  bool has_iff_guard = false;
  bool iff_guard_value = true;
  CrossOption option;
  CrossTypeOption type_option;
  bool excluded_from_coverage = false;
};

struct CrossWithMatchPolicy {
  bool require_all = false;
  uint64_t min_count = 1;
};

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

struct CoverPointOption {
  int32_t weight = 1;
  int32_t goal = 100;
  std::string comment;
  int32_t at_least = 1;
  int32_t auto_bin_max = 64;
  bool detect_overlap = false;
};

struct CoverPointTypeOption {
  int32_t weight = 1;
  int32_t goal = 100;
  std::string comment;
  double real_interval = 1.0;
};

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
  std::deque<CoverPoint> coverpoints;
  std::vector<CrossCover> crosses;
  CoverOptions options;
  uint64_t sample_count = 0;
  bool collecting = true;
  CoverGroupTypeOption type_option = {};
  std::string type_name;
};

enum class TypeOptionKind : uint8_t {
  kWeight,
  kGoal,
  kComment,
  kStrobe,
  kMergeInstances,
  kDistributeFirst,
  kRealInterval,
};

enum class CoverSyntacticLevel : uint8_t {
  kCovergroup,
  kCoverpoint,
  kCross,
};

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

enum class CrossSampleOutcome : uint8_t {
  kCounted,
  kIgnored,
  kIllegalError,
};

}  // namespace delta

#endif
