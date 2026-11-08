#pragma once

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_specify.h"
#include "simulator/specify_path_delay.h"

namespace delta {

class SimContext;
class Scheduler;

struct TerminalSelect {
  bool present = false;
  int64_t left = 0;
  int64_t right = 0;
  bool operator==(const TerminalSelect&) const = default;
};

struct DelayedSignalTarget {
  std::string name;
  bool indexed = false;
  int64_t index = 0;
};

struct TimingCheckEntry {
  TimingCheckKind kind = TimingCheckKind::kSetup;
  std::string ref_signal;
  SpecifyEdge ref_edge = SpecifyEdge::kNone;
  std::string data_signal;
  SpecifyEdge data_edge = SpecifyEdge::kNone;
  TerminalSelect ref_select;
  TerminalSelect data_select;
  DelayedSignalTarget delayed_ref;
  DelayedSignalTarget delayed_data;
  const TimingCheckDecl* decl = nullptr;

  std::vector<std::pair<char, char>> ref_edge_descriptors;
  std::vector<std::pair<char, char>> data_edge_descriptors;

  std::string inst_prefix;

  std::vector<const Expr*> source_limits;
  uint64_t limit = 0;
  uint64_t limit2 = 0;

  bool negative_timing_check_enabled = false;
  int64_t signed_limit = 0;
  int64_t signed_limit2 = 0;

  uint64_t threshold = 0;

  bool event_based_flag = false;
  bool remain_active_flag = false;

  int64_t start_edge_offset = 0;
  int64_t end_edge_offset = 0;
  int64_t delayed_signal_shift = 0;
  std::string notifier;

  std::string condition;

  SourceLoc loc;

  const Expr* ref_condition_expr = nullptr;
  const Expr* data_condition_expr = nullptr;
  const Expr* timestamp_condition_expr = nullptr;
  const Expr* timecheck_condition_expr = nullptr;
};

class SkewChecker {
 public:
  explicit SkewChecker(uint64_t limit) : limit_(limit) {}

  void ReferenceEvent(uint64_t time) {
    reference_time_ = time;
    has_reference_ = true;
  }

  bool DataEvent(uint64_t time) const {
    if (!has_reference_) return false;
    if (time <= reference_time_) return false;
    return time - reference_time_ > limit_;
  }

 private:
  uint64_t limit_;
  uint64_t reference_time_ = 0;
  bool has_reference_ = false;
};

class TimeskewChecker {
 public:
  TimeskewChecker(uint64_t limit, bool event_based_flag,
                  bool remain_active_flag)
      : limit_(limit),
        event_based_(event_based_flag),
        remain_active_(remain_active_flag) {}

  void ReferenceEvent(uint64_t time, bool condition_holds = true) {
    if (condition_holds) {
      reference_time_ = time;
      armed_ = true;
      return;
    }
    if (!remain_active_) armed_ = false;
  }

  bool DataEvent(uint64_t time) {
    if (!armed_) return false;
    if (time <= reference_time_) return false;
    uint64_t elapsed = time - reference_time_;
    if (event_based_) {
      if (elapsed <= limit_) return false;
      if (!remain_active_) armed_ = false;
      return true;
    }
    armed_ = false;
    return false;
  }

  bool Timeout() {
    if (event_based_ || !armed_) return false;
    armed_ = false;
    return true;
  }

 private:
  uint64_t limit_;
  bool event_based_;
  bool remain_active_;
  uint64_t reference_time_ = 0;
  bool armed_ = false;
};

bool ReportsTimeskewViolation(uint64_t ref_time, uint64_t next_event_time,
                              bool next_event_is_data, uint64_t limit,
                              bool event_based_flag);

bool ReportsFullskewViolation(uint64_t timestamp_time, uint64_t next_event_time,
                              bool next_event_is_timecheck, uint64_t limit,
                              bool event_based_flag);

enum class FullskewWindowAction : uint8_t {
  kReplaceWindow,
  kIgnore,
  kGoDormant,
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

struct TimingCheckConditionClass {
  TimingCheckConditionKind kind = TimingCheckConditionKind::kPlain;
  uint8_t scalar_constant_bit = 0;
};

TimingCheckConditionClass ClassifyTimingCheckCondition(const Expr* condition);

const Expr* TimingCheckConditioningSignal(const Expr* condition);

bool IsSingleSignalTimingCheck(TimingCheckKind kind);

enum class TimingCheckVectorMode : uint8_t {
  kSingle,
  kPerBit,
};

uint64_t TimingCheckExpandedCount(TimingCheckKind kind, uint32_t ref_width,
                                  uint32_t data_width,
                                  TimingCheckVectorMode mode);

uint32_t VectorTransitionViolationCount(uint64_t before, uint64_t after,
                                        uint32_t width);

bool TimingCheckUsesDelayedSignals(TimingCheckKind kind);

bool EvaluatedOnDelayedSignals(const TimingCheckEntry& check);

struct AdjustedNegativeTimingLimit {
  uint64_t limit;
  bool warn;
};

AdjustedNegativeTimingLimit AdjustNegativeTimingCheckLimit(
    int64_t adjusted_limit);

int64_t FirstLimitDelayShift(const TimingCheckEntry& check);

AdjustedNegativeTimingLimit ShiftTimingCheckLimit(uint64_t limit,
                                                  int64_t shift);

bool NegativeTimingWindowCanYieldViolation(int64_t lower, int64_t upper,
                                           uint64_t precision_ticks);

uint64_t LatchedNegativeTimingWindowValue(int64_t window_lower,
                                          int64_t window_upper,
                                          int64_t data_transition_time,
                                          uint64_t old_value,
                                          uint64_t new_value);

bool ImplicitDelayedSignalsRequired(bool negative_setup_or_hold_present,
                                    bool explicit_delayed_signals_declared);

uint64_t EffectiveOutputDelayWithTimingCheckSignalDelay(
    uint64_t propagation_delay, uint64_t timing_check_signal_delay);

struct ResolvedDelayedSignal {
  std::string signal;
  std::string delayed_name;
  bool is_explicit = false;
};

std::vector<ResolvedDelayedSignal> ResolveDelayedSignals(
    const std::vector<std::pair<std::string, std::string>>& refs);

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

enum class TimingCheckOperandKind : uint8_t {
  kReference,
  kData,
  kTimestampCondition,
  kTimecheckCondition,
};

bool OperandGetsImplicitDelayedCopy(TimingCheckOperandKind kind);

bool NegativeTimingCheckNotifierShouldToggle(bool delayed_adjusted_violation,
                                             bool undelayed_original_violation);

bool NegativeTimingCheckOptionActive(bool negative_timing_check_option_enabled,
                                     bool all_timing_checks_disabled);

int64_t EffectiveTimingCheckSignalDelay(int64_t requested_delay,
                                        bool negative_timing_option_active);

struct TimingCheckInvocationOptions {
  bool negative_timing_checks = false;
  bool all_timing_checks_off = false;
};

bool NegativeTimingCheckValuesAccepted(
    bool negative_value_present, const TimingCheckInvocationOptions& options);

struct EffectiveDelayedSignals {
  std::string ref_signal;
  int64_t ref_delay = 0;
  std::string data_signal;
  int64_t data_delay = 0;
  bool are_copies_of_originals = false;
};

EffectiveDelayedSignals ResolveDelayedSignalsUnderOptions(
    const TimingCheckDecl& decl, int64_t requested_ref_delay,
    int64_t requested_data_delay, const TimingCheckInvocationOptions& options);

TimingCheckEntry BuildTimingCheckUnderOptions(
    const TimingCheckDecl& decl, SimContext& ctx, Arena& arena,
    const TimingCheckInvocationOptions& options);

}  // namespace delta
