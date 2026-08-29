// §31: whether an observed pair of transitions violates a timing check the
// design declared. Each SpecifyManager::Check*Violation member below reads
// timing_checks_ for the entries of one TimingCheckKind and compares the time
// between the reference event and the data event against that entry's limits.
// The free functions beside them answer the rules those comparisons are made
// under: §31.7's scalar_timing_check_condition (ClassifyTimingCheckCondition,
// TimingCheckConditionEnables), §31.8's per-bit expansion of a vector signal
// (TimingCheckExpandedCount, VectorTransitionViolationCount) and §31.9's
// negative timing checks (AdjustNegativeTimingCheckLimit,
// NegativeTimingWindowCanYieldViolation, ResolveDelayedSignals).
//
// SpecifyManager::CheckSetupholdViolation stands in
// src/simulator/specify_timing_check.cpp, beside the
// BuildTimingCheckUnderOptions that fills in the TimingCheckEntry values read
// here. SpecifyManager's pulse handling -- §30.7.1's PATHPULSE$ specparams,
// §30.7.4's pulsestyle and showcancelled declarations, §32.7's SDF pulse
// limits and §32.4.3's rebuild of a path whose delay reads an annotated
// specparam -- stands in src/simulator/specify_pulse.cpp, which these
// functions were split out of.

#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/specify.h"
#include "simulator/specify_internal.h"

namespace delta {

bool SpecifyManager::CheckSetupViolation(std::string_view ref,
                                         uint64_t ref_time,
                                         std::string_view data,
                                         uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kSetup) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time < ref_time && ref_time - data_time < check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckHoldViolation(std::string_view ref, uint64_t ref_time,
                                        std::string_view data,
                                        uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kHold) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time >= ref_time && data_time - ref_time < check.limit)
      return true;
  }
  return false;
}

bool SpecifyManager::CheckRemovalViolation(std::string_view ref,
                                           uint64_t ref_time,
                                           std::string_view data,
                                           uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kRemoval) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time < ref_time && ref_time - data_time < check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckRecoveryViolation(std::string_view ref,
                                            uint64_t ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kRecovery) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time >= ref_time && data_time - ref_time < check.limit)
      return true;
  }
  return false;
}

// Shared implementation for the two-sided timing checks, $recrem and
// $setuphold. Both filter by kind and signals, then compare the data event
// against a pair of limits, and the only difference between them is which
// declared limit bounds which side of the reference time. TwoSidedLimitOrder
// (simulator/specify_internal.h) is that difference, stated once per kind by
// the member that names the kind.
namespace {

// The two limits of a two-sided check, each named for the side of the reference
// time it bounds rather than for the constraint that declared it. The signed
// pair carries the same two limits as §31.9 wrote them.
struct SidedLimits {
  uint64_t before = 0;
  uint64_t after = 0;
  int64_t signed_before = 0;
  int64_t signed_after = 0;
};

SidedLimits SidedLimitsOf(const TimingCheckEntry& check,
                          TwoSidedLimitOrder order) {
  if (order == TwoSidedLimitOrder::kSecondBoundsBefore) {
    return SidedLimits{check.limit2, check.limit, check.signed_limit2,
                       check.signed_limit};
  }
  return SidedLimits{check.limit, check.limit2, check.signed_limit,
                     check.signed_limit2};
}

// §31.9.1 requirement (a): "A timing violation shall be triggered if the signal
// changes in the violation window, exclusive of the end points." A negative
// limit moves an end point across the reference time rather than bounding one
// side of it, so the window is the one open interval the two signed limits mark
// out around that time and neither side is answered on its own.
bool NegativeTimingWindowViolated(const SidedLimits& limits, uint64_t ref_time,
                                  uint64_t data_time) {
  const auto kRefT = static_cast<int64_t>(ref_time);
  const auto kDataT = static_cast<int64_t>(data_time);
  return kDataT > kRefT - limits.signed_before &&
         kDataT < kRefT + limits.signed_after;
}

// True when the elapsed time between `ref_time` and `data_time` violates the
// limit bounding the side the data event fell on.
bool TwoSidedLimitViolated(const SidedLimits& limits, uint64_t ref_time,
                           uint64_t data_time) {
  if (limits.before == 0 && limits.after == 0) return false;
  if (data_time <= ref_time) return ref_time - data_time < limits.before;
  return data_time - ref_time < limits.after;
}

}  // namespace

bool CheckTimingViolation(const std::vector<TimingCheckEntry>& timing_checks,
                          TimingCheckKind kind, const TimingCheckEvent& event,
                          TwoSidedLimitOrder order) {
  for (const auto& check : timing_checks) {
    if (check.kind != kind) continue;
    if (check.ref_signal != event.ref) continue;
    if (check.data_signal != event.data) continue;
    const SidedLimits kLimits = SidedLimitsOf(check, order);
    if (check.negative_timing_check_enabled) {
      if (NegativeTimingWindowViolated(kLimits, event.ref_time,
                                       event.data_time)) {
        return true;
      }
      continue;
    }
    if (TwoSidedLimitViolated(kLimits, event.ref_time, event.data_time)) {
      return true;
    }
  }
  return false;
}

bool SpecifyManager::CheckRecremViolation(std::string_view ref,
                                          uint64_t ref_time,
                                          std::string_view data,
                                          uint64_t data_time) const {
  // §31.9.4: the option that switches all timing checks off suppresses this
  // check the same way it suppresses $setuphold.
  if (timing_check_options_.all_timing_checks_off) return false;
  return CheckTimingViolation(timing_checks_, TimingCheckKind::kRecrem,
                              {ref, ref_time, data, data_time},
                              TwoSidedLimitOrder::kSecondBoundsBefore);
}

bool SpecifyManager::CheckSkewViolation(std::string_view ref, uint64_t ref_time,
                                        std::string_view data,
                                        uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kSkew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time > ref_time && data_time - ref_time > check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckTimeskewViolation(std::string_view ref,
                                            uint64_t ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kTimeskew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (data_time > ref_time && data_time - ref_time > check.limit) return true;
  }
  return false;
}

namespace {

bool FullskewWindowViolated(const TimingCheckEntry& check, uint64_t ref_time,
                            uint64_t data_time) {
  if (ref_time < data_time) {
    return data_time - ref_time > check.limit;
  }
  if (data_time < ref_time) {
    return ref_time - data_time > check.limit2;
  }
  return false;
}

}  // namespace

bool SpecifyManager::CheckFullskewViolation(std::string_view ref,
                                            uint64_t ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kFullskew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (FullskewWindowViolated(check, ref_time, data_time)) return true;
  }
  return false;
}

bool SpecifyManager::CheckWidthViolation(std::string_view ref,
                                         uint64_t ref_time,
                                         uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kWidth) continue;
    if (check.ref_signal != ref) continue;

    if (data_time <= ref_time) continue;
    uint64_t elapsed = data_time - ref_time;

    if (elapsed > check.threshold && elapsed < check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckNochangeViolation(std::string_view ref,
                                            uint64_t leading_ref_time,
                                            uint64_t trailing_ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kNochange) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    int64_t begin =
        static_cast<int64_t>(leading_ref_time) - check.start_edge_offset;
    int64_t end =
        static_cast<int64_t>(trailing_ref_time) + check.end_edge_offset;
    auto t = static_cast<int64_t>(data_time);

    if (begin < t && t < end) return true;
  }
  return false;
}

bool SpecifyManager::CheckPeriodViolation(std::string_view ref,
                                          uint64_t ref_time,
                                          uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kPeriod) continue;
    if (check.ref_signal != ref) continue;

    if (data_time <= ref_time) continue;

    if (data_time - ref_time < check.limit) return true;
  }
  return false;
}

bool ReportsFullskewViolation(uint64_t timestamp_time, uint64_t next_event_time,
                              bool next_event_is_timecheck, uint64_t limit,
                              bool event_based_flag) {
  if (next_event_time <= timestamp_time) return false;
  uint64_t elapsed = next_event_time - timestamp_time;
  if (event_based_flag) {
    return next_event_is_timecheck && elapsed > limit;
  }

  return elapsed > limit;
}

FullskewWindowAction FullskewSecondTimestampAction(
    bool timestamp_condition_holds, bool remain_active_flag) {
  // A timestamp whose condition holds (or that carries no condition) always
  // opens a fresh timing window, superseding any window in progress and
  // re-arming the check if it was dormant.
  if (timestamp_condition_holds) return FullskewWindowAction::kReplaceWindow;

  // With a false condition the remain_active_flag is decisive: when set, the
  // event is discarded and the existing window stands; when clear, the check
  // turns dormant.
  if (remain_active_flag) return FullskewWindowAction::kIgnore;
  return FullskewWindowAction::kGoDormant;
}

bool ReportsTimeskewViolation(uint64_t ref_time, uint64_t next_event_time,
                              bool next_event_is_data, uint64_t limit,
                              bool event_based_flag) {
  if (next_event_time <= ref_time) return false;
  uint64_t elapsed = next_event_time - ref_time;
  if (event_based_flag) {
    return next_event_is_data && elapsed > limit;
  }

  return elapsed > limit;
}

Logic4Word ToggleNotifierOnViolation(Logic4Word current) {
  const bool kPreA = (current.aval & 1u) != 0u;
  const bool kPreB = (current.bval & 1u) != 0u;
  // z, which Table 31-13's fourth row leaves where it is.
  if (kPreB && !kPreA) return Logic4Word{0u, 1u};

  // 1, which Table 31-13's third row takes to 0.
  if (kPreA && !kPreB) return Logic4Word{0u, 0u};

  // 0, which Table 31-13's second row takes to 1, and x, whose row gives
  // "Either 0 or 1". That row is a licence rather than a value, so 0 and 1 both
  // conform and 1 is the answer chosen here; §31.6 prefers neither. The two
  // rows share this return because they were given the same answer and not
  // because the table joins them.
  return Logic4Word{1u, 0u};
}

bool IsDeterministicTimingCheckCondition(TimingCheckConditionKind kind) {
  switch (kind) {
    case TimingCheckConditionKind::kPlain:
    case TimingCheckConditionKind::kNegate:
    case TimingCheckConditionKind::kCaseEq:
    case TimingCheckConditionKind::kCaseNeq:
      return true;
    case TimingCheckConditionKind::kEq:
    case TimingCheckConditionKind::kNeq:
      return false;
  }
  return false;
}

bool TimingCheckConditionEnables(TimingCheckConditionKind kind,
                                 Logic4Word conditioning_lsb,
                                 uint8_t scalar_constant_bit) {
  const bool kNown = (conditioning_lsb.bval & 1u) == 0u;
  if (!kNown) {
    return !IsDeterministicTimingCheckCondition(kind);
  }
  const auto kBit = static_cast<uint8_t>(conditioning_lsb.aval & 1u);
  const auto kRhs = static_cast<uint8_t>(scalar_constant_bit & 1u);
  switch (kind) {
    case TimingCheckConditionKind::kPlain:
      return kBit == 1u;
    case TimingCheckConditionKind::kNegate:
      return kBit == 0u;
    case TimingCheckConditionKind::kEq:
    case TimingCheckConditionKind::kCaseEq:
      return kBit == kRhs;
    case TimingCheckConditionKind::kNeq:
    case TimingCheckConditionKind::kCaseNeq:
      return kBit != kRhs;
  }
  return false;
}

TimingCheckConditionClass ClassifyTimingCheckCondition(const Expr* condition) {
  TimingCheckConditionClass result;
  if (condition == nullptr) return result;  // unconditioned event -> plain

  // `~ expression`: the bitwise-negation form of scalar_timing_check_condition.
  if (condition->kind == ExprKind::kUnary &&
      condition->op == TokenKind::kTilde) {
    result.kind = TimingCheckConditionKind::kNegate;
    return result;
  }

  // `expression <op> scalar_constant`: the four comparison forms. The LSB of
  // the right-hand scalar_constant is the value compared against.
  if (condition->kind == ExprKind::kBinary) {
    bool matched = true;
    switch (condition->op) {
      case TokenKind::kEqEq:
        result.kind = TimingCheckConditionKind::kEq;
        break;
      case TokenKind::kEqEqEq:
        result.kind = TimingCheckConditionKind::kCaseEq;
        break;
      case TokenKind::kBangEq:
        result.kind = TimingCheckConditionKind::kNeq;
        break;
      case TokenKind::kBangEqEq:
        result.kind = TimingCheckConditionKind::kCaseNeq;
        break;
      default:
        matched = false;
        break;
    }
    if (matched) {
      if (condition->rhs != nullptr) {
        result.scalar_constant_bit =
            static_cast<uint8_t>(condition->rhs->int_val & 1u);
      }
      return result;
    }
  }

  // Any other expression is the plain form: its own value gates the check.
  return result;
}

const Expr* TimingCheckConditioningSignal(const Expr* condition) {
  if (condition == nullptr) return nullptr;
  // `~ expression`: the negation is applied by TimingCheckConditionEnables, so
  // the operand is what carries the conditioning signal's value. A unary node
  // holds its operand in lhs.
  if (condition->kind == ExprKind::kUnary &&
      condition->op == TokenKind::kTilde) {
    return condition->lhs;
  }
  // `expression <op> scalar_constant`: the comparison is applied by
  // TimingCheckConditionEnables against the scalar_constant it already carries,
  // so the left-hand operand is the conditioning signal.
  if (condition->kind == ExprKind::kBinary) {
    switch (condition->op) {
      case TokenKind::kEqEq:
      case TokenKind::kEqEqEq:
      case TokenKind::kBangEq:
      case TokenKind::kBangEqEq:
        return condition->lhs;
      default:
        break;
    }
  }
  // Any other expression is the plain form, whose own value gates the check --
  // the same expression ClassifyTimingCheckCondition reports as kPlain.
  return condition;
}

bool IsSingleSignalTimingCheck(TimingCheckKind kind) {
  return kind == TimingCheckKind::kWidth || kind == TimingCheckKind::kPeriod;
}

uint64_t TimingCheckExpandedCount(TimingCheckKind kind, uint32_t ref_width,
                                  uint32_t data_width,
                                  TimingCheckVectorMode mode) {
  if (mode == TimingCheckVectorMode::kSingle) return 1u;

  if (IsSingleSignalTimingCheck(kind)) {
    return static_cast<uint64_t>(ref_width);
  }
  return static_cast<uint64_t>(ref_width) * static_cast<uint64_t>(data_width);
}

uint32_t VectorTransitionViolationCount(uint64_t before, uint64_t after,
                                        uint32_t width) {
  if (width == 0) return 0u;
  // Mask off any bits beyond the vector width, then count the positions whose
  // value differs -- each is one single-bit transition, hence one violation.
  uint64_t mask = (width >= 64u) ? ~uint64_t{0} : ((uint64_t{1} << width) - 1u);
  uint64_t changed = (before ^ after) & mask;
  uint32_t count = 0;
  while (changed != 0) {
    changed &= (changed - 1u);
    ++count;
  }
  return count;
}

bool TimingCheckUsesDelayedSignals(TimingCheckKind kind) {
  switch (kind) {
    case TimingCheckKind::kSetup:
    case TimingCheckKind::kHold:
    case TimingCheckKind::kSetuphold:
    case TimingCheckKind::kRecovery:
    case TimingCheckKind::kRemoval:
    case TimingCheckKind::kRecrem:
    case TimingCheckKind::kWidth:
    case TimingCheckKind::kPeriod:
    case TimingCheckKind::kNochange:
      return true;

    case TimingCheckKind::kSkew:
    case TimingCheckKind::kFullskew:
    case TimingCheckKind::kTimeskew:
      return false;
  }
  return false;
}

AdjustedNegativeTimingLimit AdjustNegativeTimingCheckLimit(
    int64_t adjusted_limit) {
  if (adjusted_limit <= 0) {
    return {0u, true};
  }
  return {static_cast<uint64_t>(adjusted_limit), false};
}

bool NegativeTimingWindowCanYieldViolation(int64_t lower, int64_t upper,
                                           uint64_t precision_ticks) {
  if (upper <= lower) return false;

  const int64_t kMinWidth = 2 * static_cast<int64_t>(precision_ticks);
  return (upper - lower) >= kMinWidth;
}

uint64_t LatchedNegativeTimingWindowValue(int64_t window_lower,
                                          int64_t window_upper,
                                          int64_t data_transition_time,
                                          uint64_t old_value,
                                          uint64_t new_value) {
  (void)window_upper;
  // The new value is stable across the excluded-endpoint interior only when the
  // data has already settled by the time the window opens; a change at or after
  // the open boundary leaves the old value as the stable (and, inside the
  // window, incorrectly clocked) one.
  return data_transition_time <= window_lower ? new_value : old_value;
}

bool ImplicitDelayedSignalsRequired(bool negative_setup_or_hold_present,
                                    bool explicit_delayed_signals_declared) {
  return negative_setup_or_hold_present && !explicit_delayed_signals_declared;
}

uint64_t EffectiveOutputDelayWithTimingCheckSignalDelay(
    uint64_t propagation_delay, uint64_t timing_check_signal_delay) {
  return timing_check_signal_delay > propagation_delay
             ? timing_check_signal_delay
             : propagation_delay;
}

std::vector<ResolvedDelayedSignal> ResolveDelayedSignals(
    const std::vector<std::pair<std::string, std::string>>& refs) {
  std::vector<ResolvedDelayedSignal> resolved;
  for (const auto& [signal, delayed_name] : refs) {
    ResolvedDelayedSignal* existing = nullptr;
    for (auto& entry : resolved) {
      if (entry.signal == signal) {
        existing = &entry;
        break;
      }
    }
    if (existing == nullptr) {
      // First time this signal is seen: one copy, explicit if declared here.
      resolved.push_back({signal, delayed_name, !delayed_name.empty()});
      continue;
    }
    // The signal already has its single shared copy. If this check supplies an
    // explicit name and the copy is still implicit, promote it -- an explicit
    // declaration in any referencing check is used for all of them.
    if (!existing->is_explicit && !delayed_name.empty()) {
      existing->delayed_name = delayed_name;
      existing->is_explicit = true;
    }
  }
  return resolved;
}

bool ZeroSmallestNegativeTimingLimit(std::vector<int64_t>& limits) {
  size_t best_index = limits.size();
  for (size_t i = 0; i < limits.size(); ++i) {
    if (limits[i] >= 0) continue;
    if (best_index == limits.size() || limits[i] > limits[best_index]) {
      best_index = i;
    }
  }
  if (best_index == limits.size()) return false;
  limits[best_index] = 0;
  return true;
}

NegativeTimingConditionRole TimestampConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold) {
  if (signed_setup < 0 && signed_hold < 0) {
    return NegativeTimingConditionRole::kNone;
  }

  if (signed_setup < 0) return NegativeTimingConditionRole::kRef;

  if (signed_hold < 0) return NegativeTimingConditionRole::kData;

  return NegativeTimingConditionRole::kBoth;
}

}  // namespace delta
