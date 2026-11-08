#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_specify.h"
#include "simulator/specify.h"
#include "simulator/specify_internal.h"
#include "simulator/specify_timing_check.h"

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

namespace {

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

bool NegativeTimingWindowViolated(const SidedLimits& limits, uint64_t ref_time,
                                  uint64_t data_time) {
  const auto kRefT = static_cast<int64_t>(ref_time);
  const auto kDataT = static_cast<int64_t>(data_time);
  return kDataT > kRefT - limits.signed_before &&
         kDataT < kRefT + limits.signed_after;
}

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
  if (timestamp_condition_holds) return FullskewWindowAction::kReplaceWindow;

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
  if (kPreB && !kPreA) return Logic4Word{0u, 1u};

  if (kPreA && !kPreB) return Logic4Word{0u, 0u};

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

static bool IsScalarConstant(const Expr* e) {
  if (e->kind != ExprKind::kIntegerLiteral) return false;
  static constexpr std::string_view kSpellings[] = {
      "1'b0", "1'b1", "1'B0", "1'B1", "'b0", "'b1", "'B0", "'B1", "1", "0"};
  for (std::string_view spelling : kSpellings) {
    if (e->text == spelling) return true;
  }
  return false;
}

static TimingCheckConditionKind ComparisonFormOf(const Expr* condition) {
  if (condition->kind != ExprKind::kBinary) {
    return TimingCheckConditionKind::kPlain;
  }
  TimingCheckConditionKind kind = TimingCheckConditionKind::kPlain;
  switch (condition->op) {
    case TokenKind::kEqEq:
      kind = TimingCheckConditionKind::kEq;
      break;
    case TokenKind::kEqEqEq:
      kind = TimingCheckConditionKind::kCaseEq;
      break;
    case TokenKind::kBangEq:
      kind = TimingCheckConditionKind::kNeq;
      break;
    case TokenKind::kBangEqEq:
      kind = TimingCheckConditionKind::kCaseNeq;
      break;
    default:
      break;
  }
  return IsScalarConstant(condition->rhs) ? kind
                                          : TimingCheckConditionKind::kPlain;
}

TimingCheckConditionClass ClassifyTimingCheckCondition(const Expr* condition) {
  TimingCheckConditionClass result;
  if (condition == nullptr) return result;

  if (condition->kind == ExprKind::kUnary &&
      condition->op == TokenKind::kTilde) {
    result.kind = TimingCheckConditionKind::kNegate;
    return result;
  }

  result.kind = ComparisonFormOf(condition);
  if (result.kind != TimingCheckConditionKind::kPlain) {
    result.scalar_constant_bit =
        static_cast<uint8_t>(condition->rhs->int_val & 1u);
  }
  return result;
}

const Expr* TimingCheckConditioningSignal(const Expr* condition) {
  if (condition == nullptr) return nullptr;
  if (condition->kind == ExprKind::kUnary &&
      condition->op == TokenKind::kTilde) {
    return condition->lhs;
  }
  if (ComparisonFormOf(condition) != TimingCheckConditionKind::kPlain) {
    return condition->lhs;
  }
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
      resolved.push_back({signal, delayed_name, !delayed_name.empty()});
      continue;
    }
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
