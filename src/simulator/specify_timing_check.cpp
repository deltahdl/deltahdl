#include "simulator/specify_timing_check.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_specify.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_internal.h"

namespace delta {

NegativeTimingConditionRole TimecheckConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold) {
  if (signed_setup < 0 && signed_hold < 0) {
    return NegativeTimingConditionRole::kNone;
  }
  if (signed_setup < 0) return NegativeTimingConditionRole::kData;
  if (signed_hold < 0) return NegativeTimingConditionRole::kRef;
  return NegativeTimingConditionRole::kBoth;
}

bool OperandGetsImplicitDelayedCopy(TimingCheckOperandKind kind) {
  return kind == TimingCheckOperandKind::kReference ||
         kind == TimingCheckOperandKind::kData;
}

bool NegativeTimingCheckNotifierShouldToggle(bool delayed_adjusted_violation,
                                             bool) {
  return delayed_adjusted_violation;
}

bool NegativeTimingCheckOptionActive(bool negative_timing_check_option_enabled,
                                     bool all_timing_checks_disabled) {
  return negative_timing_check_option_enabled && !all_timing_checks_disabled;
}

int64_t EffectiveTimingCheckSignalDelay(int64_t requested_delay,
                                        bool negative_timing_option_active) {
  if (!negative_timing_option_active) return 0;
  return requested_delay;
}

bool NegativeTimingCheckValuesAccepted(
    bool negative_value_present, const TimingCheckInvocationOptions& options) {
  return negative_value_present &&
         NegativeTimingCheckOptionActive(options.negative_timing_checks,
                                         options.all_timing_checks_off);
}

EffectiveDelayedSignals ResolveDelayedSignalsUnderOptions(
    const TimingCheckDecl& decl, int64_t requested_ref_delay,
    int64_t requested_data_delay, const TimingCheckInvocationOptions& options) {
  const bool kActive = NegativeTimingCheckOptionActive(
      options.negative_timing_checks, options.all_timing_checks_off);

  const std::string kRefOriginal = SpecifyTerminalName(decl.ref_terminal);
  const std::string kDataOriginal = SpecifyTerminalName(decl.data_terminal);

  EffectiveDelayedSignals out;
  out.are_copies_of_originals = !kActive;
  if (!kActive) {
    out.ref_signal = kRefOriginal;
    out.data_signal = kDataOriginal;
    out.ref_delay = EffectiveTimingCheckSignalDelay(requested_ref_delay, false);
    out.data_delay =
        EffectiveTimingCheckSignalDelay(requested_data_delay, false);
    return out;
  }

  out.ref_signal =
      decl.delayed_ref.empty() ? kRefOriginal : std::string(decl.delayed_ref);
  out.data_signal = decl.delayed_data.empty() ? kDataOriginal
                                              : std::string(decl.delayed_data);
  out.ref_delay = EffectiveTimingCheckSignalDelay(requested_ref_delay, true);
  out.data_delay = EffectiveTimingCheckSignalDelay(requested_data_delay, true);
  return out;
}

namespace {

int64_t EvalTimingCheckLimit(Expr* limit, SimContext& ctx, Arena& arena) {
  if (limit == nullptr) return 0;
  Logic4Vec value = EvalExpr(limit, ctx, arena);
  const uint32_t kWidth = value.width == 0 ? 64u : value.width;
  return SignExtend(value.ToUint64(), kWidth);
}

int64_t EvalTimingCheckTime(Expr* limit, SimContext& ctx, Arena& arena) {
  if (limit == nullptr) return 0;
  Logic4Vec value = EvalExpr(limit, ctx, arena);
  const TimeScale& scale = ActiveInstanceTimeScale(ctx);
  if (value.is_real) {
    const double kReal = RealVecToDouble(value);
    const auto kTicks = static_cast<int64_t>(RealDelayToTicks(
        kReal < 0 ? -kReal : kReal, scale, ctx.GlobalPrecision()));
    return kReal < 0 ? -kTicks : kTicks;
  }
  const uint32_t kWidth = value.width == 0 ? 64u : value.width;
  const int64_t kSigned = SignExtend(value.ToUint64(), kWidth);
  const uint64_t kMagnitude = kSigned < 0
                                  ? 0ULL - static_cast<uint64_t>(kSigned)
                                  : static_cast<uint64_t>(kSigned);
  const auto kTicks = static_cast<int64_t>(
      DelayToTicks(kMagnitude, scale, ctx.GlobalPrecision()));
  return kSigned < 0 ? -kTicks : kTicks;
}

std::vector<std::pair<char, char>> RunTimeEdgeDescriptors(
    const std::vector<std::pair<char, char>>& parsed) {
  auto fold = [](char c) { return c == '0' || c == '1' ? c : 'x'; };
  std::vector<std::pair<char, char>> folded;
  folded.reserve(parsed.size());
  for (const std::pair<char, char>& descriptor : parsed) {
    folded.emplace_back(fold(descriptor.first), fold(descriptor.second));
  }
  return folded;
}

uint64_t UnhandledNegativeLimit(int64_t signed_limit) {
  return signed_limit < 0 ? 0u : static_cast<uint64_t>(signed_limit);
}

DelayedSignalTarget DelayedTargetOf(std::string_view name, const Expr* index,
                                    SimContext& ctx, Arena& arena) {
  DelayedSignalTarget target;
  target.name = std::string(name);
  if (index != nullptr) {
    target.indexed = true;
    target.index = SelectBoundValue(EvalExpr(index, ctx, arena));
  }
  return target;
}

}  // namespace

TimingCheckEntry BuildTimingCheckUnderOptions(
    const TimingCheckDecl& decl, SimContext& ctx, Arena& arena,
    const TimingCheckInvocationOptions& options) {
  TimingCheckEntry entry;
  entry.kind = decl.check_kind;
  entry.decl = &decl;
  entry.source_limits.assign(decl.limits.begin(), decl.limits.end());
  entry.ref_signal = SpecifyTerminalName(decl.ref_terminal);
  entry.ref_edge = decl.ref_edge;
  entry.data_signal = SpecifyTerminalName(decl.data_terminal);
  entry.ref_select = SpecifyTerminalSelect(decl.ref_terminal, ctx, arena);
  entry.data_select = SpecifyTerminalSelect(decl.data_terminal, ctx, arena);
  entry.delayed_ref =
      DelayedTargetOf(decl.delayed_ref, decl.delayed_ref_expr, ctx, arena);
  entry.delayed_data =
      DelayedTargetOf(decl.delayed_data, decl.delayed_data_expr, ctx, arena);
  entry.data_edge = decl.data_edge;
  entry.notifier = std::string(decl.notifier);
  entry.loc = decl.loc;

  entry.event_based_flag =
      EvalTimingCheckLimit(decl.event_based_flag, ctx, arena) != 0;
  entry.remain_active_flag =
      EvalTimingCheckLimit(decl.remain_active_flag, ctx, arena) != 0;

  entry.ref_edge_descriptors =
      RunTimeEdgeDescriptors(decl.ref_edge_descriptors);
  entry.data_edge_descriptors =
      RunTimeEdgeDescriptors(decl.data_edge_descriptors);

  entry.condition = SpecifyConditionText(decl.ref_condition);
  if (entry.condition.empty()) {
    entry.condition = SpecifyConditionText(decl.data_condition);
  }

  entry.ref_condition_expr = decl.ref_condition;
  entry.data_condition_expr = decl.data_condition;
  entry.timestamp_condition_expr = decl.timestamp_cond;
  entry.timecheck_condition_expr = decl.timecheck_cond;

  const int64_t kFirst = EvalTimingCheckTime(
      decl.limits.empty() ? nullptr : decl.limits[0], ctx, arena);
  const int64_t kSecond = EvalTimingCheckTime(
      decl.limits.size() < 2 ? nullptr : decl.limits[1], ctx, arena);

  if (decl.check_kind == TimingCheckKind::kNochange) {
    entry.start_edge_offset = kFirst;
    entry.end_edge_offset = kSecond;
    return entry;
  }

  const bool kIsWidth = decl.check_kind == TimingCheckKind::kWidth;
  const int64_t kSecondLimit = kIsWidth ? 0 : kSecond;

  entry.signed_limit = kFirst;
  entry.signed_limit2 = kSecondLimit;

  const bool kNegativePresent = kFirst < 0 || kSecondLimit < 0;
  entry.negative_timing_check_enabled =
      NegativeTimingCheckValuesAccepted(kNegativePresent, options);

  entry.limit = UnhandledNegativeLimit(kFirst);
  entry.limit2 = UnhandledNegativeLimit(kSecondLimit);
  if (kIsWidth) entry.threshold = UnhandledNegativeLimit(kSecond);
  return entry;
}

void SpecifyManager::SetTimingCheckInvocationOptions(
    TimingCheckInvocationOptions options) {
  timing_check_options_ = options;
  ApplyTimingCheckInvocationOptions();
}

void SpecifyManager::ApplyTimingCheckInvocationOptions() {
  if (NegativeTimingCheckOptionActive(
          timing_check_options_.negative_timing_checks,
          timing_check_options_.all_timing_checks_off)) {
    return;
  }
  for (auto& check : timing_checks_) {
    if (!check.negative_timing_check_enabled) continue;
    check.negative_timing_check_enabled = false;
    if (check.signed_limit < 0) {
      check.limit = UnhandledNegativeLimit(check.signed_limit);
    }
    if (check.signed_limit2 < 0) {
      check.limit2 = UnhandledNegativeLimit(check.signed_limit2);
    }
  }
}

void SpecifyManager::AddTimingCheckUnderOptions(const TimingCheckDecl& decl,
                                                SimContext& ctx, Arena& arena,
                                                std::string_view inst_prefix) {
  TimingCheckEntry entry =
      BuildTimingCheckUnderOptions(decl, ctx, arena, timing_check_options_);
  entry.inst_prefix = inst_prefix;
  AddTimingCheck(std::move(entry));
  for (const auto& seen : timing_check_decls_) {
    if (seen.decl == &decl && seen.inst_prefix == inst_prefix) return;
  }
  timing_check_decls_.push_back({&decl, std::string(inst_prefix)});
}

bool SpecifyManager::CheckSetupholdViolation(std::string_view ref,
                                             uint64_t ref_time,
                                             std::string_view data,
                                             uint64_t data_time) const {
  if (timing_check_options_.all_timing_checks_off) return false;
  return CheckTimingViolation(timing_checks_, TimingCheckKind::kSetuphold,
                              {ref, ref_time, data, data_time},
                              TwoSidedLimitOrder::kFirstBoundsBefore);
}

}  // namespace delta
