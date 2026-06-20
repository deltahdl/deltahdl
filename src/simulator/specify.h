#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"

namespace delta {

struct PathDelay {
  std::string src_port;
  std::string dst_port;
  SpecifyPathKind path_kind = SpecifyPathKind::kParallel;
  SpecifyEdge edge = SpecifyEdge::kNone;

  std::string condition;

  bool is_ifnone = false;
  uint8_t delay_count = 1;
  uint64_t delays[12] = {};

  uint64_t reject_limit[12] = {};
  uint64_t error_limit[12] = {};
};

uint64_t ClampPathDelay(int64_t signed_value);

void ExpandTransitionDelays(PathDelay& pd);

struct PathCandidate {
  const PathDelay* path = nullptr;
  uint64_t last_transition_time = 0;
  bool condition_true = true;
};

uint64_t SelectPathDelay(const std::vector<PathCandidate>& candidates,
                         uint8_t transition_slot);

// §30.4.4.1: decide whether a state-dependent module path's conditional
// expression makes the path active. The path is active when the condition is
// true (1); an x or z result is taken as true; a multi-bit result is
// represented by its LSB, so the caller passes the least-significant 4-state
// word. The returned value is what PathCandidate::condition_true holds.
bool StateDependentPathConditionEnables(Logic4Word condition_lsb);

uint64_t SelectEffectivePathDelay(uint64_t module_path_delay,
                                  uint64_t distributed_delay_sum);

enum class PulseClassification : uint8_t {
  kPropagate,
  kForceX,
  kReject,
};

PulseClassification ClassifyPulse(uint64_t pulse_width, uint64_t reject_limit,
                                  uint64_t error_limit);

void InitDefaultPulseLimits(PathDelay& pd);

void ApplyPulseControlOverride(PathDelay& pd, uint64_t reject, bool has_error,
                               uint64_t error);

void ApplyGlobalPulseLimits(PathDelay& pd, uint8_t reject_pct,
                            uint8_t error_pct);

void ApplySdfPulseLimits(PathDelay& pd, uint64_t reject, bool has_error,
                         uint64_t error);

struct TimingCheckEntry {
  TimingCheckKind kind = TimingCheckKind::kSetup;
  std::string ref_signal;
  SpecifyEdge ref_edge = SpecifyEdge::kNone;
  std::string data_signal;
  SpecifyEdge data_edge = SpecifyEdge::kNone;
  uint64_t limit = 0;
  uint64_t limit2 = 0;

  bool negative_timing_check_enabled = false;
  int64_t signed_limit = 0;
  int64_t signed_limit2 = 0;

  uint64_t threshold = 0;

  int64_t start_edge_offset = 0;
  int64_t end_edge_offset = 0;
  std::string notifier;

  std::string condition;
};

bool ReportsTimeskewViolation(uint64_t ref_time, uint64_t next_event_time,
                              bool next_event_is_data, uint64_t limit,
                              bool event_based_flag);

bool ReportsFullskewViolation(uint64_t timestamp_time, uint64_t next_event_time,
                              bool next_event_is_timecheck, uint64_t limit,
                              bool event_based_flag);

// Effect of a fresh timestamp event on a $fullskew check (§31.4.3
// remain_active_flag semantics; identical in timer-based and event-based
// modes).
enum class FullskewWindowAction : uint8_t {
  kReplaceWindow,  // condition holds: a new window supersedes the open one /
                   // re-arms
  kIgnore,  // condition false but remain_active_flag set: event has no effect
  kGoDormant,  // condition false and remain_active_flag clear: check goes
               // dormant
};

FullskewWindowAction FullskewSecondTimestampAction(
    bool timestamp_condition_holds, bool remain_active_flag);

Logic4Word ToggleNotifierOnViolation(Logic4Word current);

enum class TimingCheckConditionKind : uint8_t {
  kPlain,
  kNegate,
  kEq,
  kCaseEq,
  kNeq,
  kCaseNeq,
};

bool IsDeterministicTimingCheckCondition(TimingCheckConditionKind kind);

bool TimingCheckConditionEnables(TimingCheckConditionKind kind,
                                 Logic4Word conditioning_lsb,
                                 uint8_t scalar_constant_bit);

bool IsSingleSignalTimingCheck(TimingCheckKind kind);

enum class TimingCheckVectorMode : uint8_t {
  kSingle,
  kPerBit,
};

uint64_t TimingCheckExpandedCount(TimingCheckKind kind, uint32_t ref_width,
                                  uint32_t data_width,
                                  TimingCheckVectorMode mode);

bool TimingCheckUsesDelayedSignals(TimingCheckKind kind);

struct AdjustedNegativeTimingLimit {
  uint64_t limit;
  bool warn;
};

AdjustedNegativeTimingLimit AdjustNegativeTimingCheckLimit(
    int64_t adjusted_limit);

bool NegativeTimingWindowCanYieldViolation(int64_t lower, int64_t upper,
                                           uint64_t precision_ticks);

bool ZeroSmallestNegativeTimingLimit(std::vector<int64_t>& limits);

enum class NegativeTimingConditionRole : uint8_t {
  kData,
  kRef,
  kBoth,
  kNone,
};

NegativeTimingConditionRole TimestampConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold);

NegativeTimingConditionRole TimecheckConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold);

bool NegativeTimingCheckNotifierShouldToggle(bool delayed_adjusted_violation,
                                             bool undelayed_original_violation);

bool NegativeTimingCheckOptionActive(bool negative_timing_check_option_enabled,
                                     bool all_timing_checks_disabled);

int64_t EffectiveTimingCheckSignalDelay(int64_t requested_delay,
                                        bool negative_timing_option_active);

struct SdfAnnotation {
  std::string sdf_file;
  std::string scope;
};

struct SpecparamValue {
  std::string name;
  uint64_t value = 0;
};

struct InterconnectDelay {
  std::string src_port;
  std::string dst_port;
  uint64_t rise = 0;
  uint64_t fall = 0;
  uint64_t delays[12] = {};
  uint64_t reject_limit[12] = {};
  uint64_t error_limit[12] = {};
};

struct SdfTcAnnotation {
  TimingCheckKind kind = TimingCheckKind::kSetup;
  std::string ref_signal;
  SpecifyEdge ref_edge = SpecifyEdge::kNone;
  std::string data_signal;
  SpecifyEdge data_edge = SpecifyEdge::kNone;
  std::string condition;
  uint64_t limit = 0;
  uint64_t limit2 = 0;
  int64_t start_edge_offset = 0;
  int64_t end_edge_offset = 0;
  bool set_limit = false;
  bool set_limit2 = false;
  bool set_start_edge_offset = false;
  bool set_end_edge_offset = false;
};

class SpecifyManager {
 public:
  void AddPathDelay(PathDelay delay, bool preserve_pulse_limits = false);

  void IncrementPathDelay(const PathDelay& delta);
  void AddTimingCheck(TimingCheckEntry check);

  void AnnotateSdfTimingCheck(const SdfTcAnnotation& annotation);

  void AnnotateSdf(SdfAnnotation annotation);
  void SetSpecparamValue(SpecparamValue spec);

  void IncrementSpecparamValue(SpecparamValue delta);
  void AddInterconnectDelay(InterconnectDelay delay);

  void IncrementInterconnectDelay(const InterconnectDelay& delta);

  void RegisterSpecparamReevaluation(std::string name,
                                     std::function<void(uint64_t)> reevaluate);

  void AddSdfPulseLimit(std::string_view src, std::string_view dst,
                        uint64_t reject, bool has_error, uint64_t error,
                        bool is_percent);

  void IncrementSdfPulseLimit(std::string_view src, std::string_view dst,
                              int64_t reject_delta, bool has_error,
                              int64_t error_delta);

  void SetGlobalPulseLimitPercents(uint8_t reject_pct, uint8_t error_pct);

  uint8_t RejectPulseLimitPercent() const { return reject_pulse_pct_; }
  uint8_t ErrorPulseLimitPercent() const { return error_pulse_pct_; }

  const std::vector<SpecparamValue>& GetSpecparamValues() const {
    return specparam_values_;
  }
  const std::vector<InterconnectDelay>& GetInterconnectDelays() const {
    return interconnect_delays_;
  }

  uint64_t GetPathDelay(std::string_view src, std::string_view dst) const;
  const std::vector<PathDelay>& GetPathDelays() const { return path_delays_; }

  const std::vector<TimingCheckEntry>& GetTimingChecks() const {
    return timing_checks_;
  }

  const std::vector<SdfAnnotation>& GetSdfAnnotations() const {
    return sdf_annotations_;
  }

  bool HasPathDelay(std::string_view src, std::string_view dst) const;
  bool CheckSetupViolation(std::string_view ref, uint64_t ref_time,
                           std::string_view data, uint64_t data_time) const;
  bool CheckHoldViolation(std::string_view ref, uint64_t ref_time,
                          std::string_view data, uint64_t data_time) const;

  bool CheckSetupholdViolation(std::string_view ref, uint64_t ref_time,
                               std::string_view data, uint64_t data_time) const;

  bool CheckRemovalViolation(std::string_view ref, uint64_t ref_time,
                             std::string_view data, uint64_t data_time) const;

  bool CheckRecoveryViolation(std::string_view ref, uint64_t ref_time,
                              std::string_view data, uint64_t data_time) const;

  bool CheckRecremViolation(std::string_view ref, uint64_t ref_time,
                            std::string_view data, uint64_t data_time) const;

  bool CheckSkewViolation(std::string_view ref, uint64_t ref_time,
                          std::string_view data, uint64_t data_time) const;

  bool CheckTimeskewViolation(std::string_view ref, uint64_t ref_time,
                              std::string_view data, uint64_t data_time) const;

  bool CheckFullskewViolation(std::string_view ref, uint64_t ref_time,
                              std::string_view data, uint64_t data_time) const;

  bool CheckWidthViolation(std::string_view ref, uint64_t ref_time,
                           uint64_t data_time) const;

  bool CheckPeriodViolation(std::string_view ref, uint64_t ref_time,
                            uint64_t data_time) const;

  bool CheckNochangeViolation(std::string_view ref, uint64_t leading_ref_time,
                              uint64_t trailing_ref_time, std::string_view data,
                              uint64_t data_time) const;

  uint32_t PathDelayCount() const {
    return static_cast<uint32_t>(path_delays_.size());
  }
  uint32_t TimingCheckCount() const {
    return static_cast<uint32_t>(timing_checks_.size());
  }

 private:
  std::vector<PathDelay> path_delays_;
  std::vector<TimingCheckEntry> timing_checks_;
  std::vector<SdfAnnotation> sdf_annotations_;

  std::vector<SpecparamValue> specparam_values_;
  std::unordered_map<std::string, size_t> specparam_index_;
  std::vector<InterconnectDelay> interconnect_delays_;

  std::vector<std::pair<std::string, std::function<void(uint64_t)>>>
      specparam_reevaluators_;

  uint8_t reject_pulse_pct_ = 100;
  uint8_t error_pulse_pct_ = 100;
};

}  // namespace delta
