#include "simulator/timing_check_stability.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <memory>
#include <string>
#include <utility>

#include "common/types.h"
#include "parser/ast_specify.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"
#include "simulator/timing_check_driver_internal.h"

namespace delta {
namespace {

enum class StabilitySide : uint8_t {
  kNone,
  kBefore,
  kAfter,
};

enum class StabilityEvent : uint8_t {
  kReference,
  kData,
};

struct TwoSidedLimits {
  uint64_t before = 0;
  uint64_t after = 0;
  int64_t signed_before = 0;
  int64_t signed_after = 0;
};

TwoSidedLimits LimitsOf(const TimingCheckEntry& check) {
  if (check.kind == TimingCheckKind::kRecrem) {
    return TwoSidedLimits{check.limit2, check.limit, check.signed_limit2,
                          check.signed_limit};
  }
  return TwoSidedLimits{check.limit, check.limit2, check.signed_limit,
                        check.signed_limit2};
}

bool TwoSidedWindowViolated(const TwoSidedLimits& limits, uint64_t ref_ticks,
                            uint64_t data_ticks) {
  if (limits.before == 0 && limits.after == 0) return false;
  if (data_ticks <= ref_ticks) return ref_ticks - data_ticks < limits.before;
  return data_ticks - ref_ticks < limits.after;
}

bool NegativeWindowViolated(const TwoSidedLimits& limits, uint64_t ref_ticks,
                            uint64_t data_ticks) {
  const auto kRefTicks = static_cast<int64_t>(ref_ticks);
  const auto kDataTicks = static_cast<int64_t>(data_ticks);
  return kDataTicks > kRefTicks - limits.signed_before &&
         kDataTicks < kRefTicks + limits.signed_after;
}

bool RemovalWindowViolated(uint64_t limit, uint64_t ref_ticks,
                           uint64_t data_ticks) {
  return data_ticks < ref_ticks && ref_ticks - data_ticks < limit;
}

bool RecoveryWindowViolated(uint64_t limit, uint64_t ref_ticks,
                            uint64_t data_ticks) {
  return data_ticks >= ref_ticks && data_ticks - ref_ticks < limit;
}

StabilitySide TwoSidedSide(const SpecifyManager& mgr,
                           const TimingCheckEntry& check, uint64_t ref_ticks,
                           uint64_t data_ticks) {
  if (mgr.GetTimingCheckInvocationOptions().all_timing_checks_off) {
    return StabilitySide::kNone;
  }
  TwoSidedLimits limits = LimitsOf(check);
  bool violated = check.negative_timing_check_enabled
                      ? NegativeWindowViolated(limits, ref_ticks, data_ticks)
                      : TwoSidedWindowViolated(limits, ref_ticks, data_ticks);
  if (!violated) return StabilitySide::kNone;
  return data_ticks <= ref_ticks ? StabilitySide::kBefore
                                 : StabilitySide::kAfter;
}

StabilitySide ViolatedSide(const SpecifyManager& mgr,
                           const TimingCheckEntry& check, uint64_t ref_ticks,
                           uint64_t data_ticks) {
  if (check.kind == TimingCheckKind::kSetuphold ||
      check.kind == TimingCheckKind::kRecrem) {
    return TwoSidedSide(mgr, check, ref_ticks, data_ticks);
  }
  if (check.kind == TimingCheckKind::kRemoval) {
    return RemovalWindowViolated(check.limit, ref_ticks, data_ticks)
               ? StabilitySide::kBefore
               : StabilitySide::kNone;
  }
  return RecoveryWindowViolated(check.limit, ref_ticks, data_ticks)
             ? StabilitySide::kAfter
             : StabilitySide::kNone;
}

bool ClosesWindow(TimingCheckKind kind, StabilityEvent event) {
  if (kind == TimingCheckKind::kRemoval) {
    return event == StabilityEvent::kReference;
  }
  if (kind == TimingCheckKind::kRecovery) {
    return event == StabilityEvent::kData;
  }
  return true;
}

struct EventConditions {
  bool timestamp = true;
  bool timecheck = true;
};

EventConditions ConditionsNow(const TimingCheckEntry& check, SimContext& ctx) {
  return {TimingCheckEventEnabled(check.timestamp_condition_expr,
                                  check.inst_prefix, ctx),
          TimingCheckEventEnabled(check.timecheck_condition_expr,
                                  check.inst_prefix, ctx)};
}

struct StabilityPair {
  ArmedCheck armed;
  std::string ref_signal;
  std::string data_signal;
  bool has_ref = false;
  uint64_t ref_ticks = 0;
  bool has_data = false;
  uint64_t data_ticks = 0;
  EventConditions ref_conditions;
  EventConditions data_conditions;

  std::shared_ptr<bool> pending = std::make_shared<bool>(false);
};

void ReportSetuphold(StabilitySide side, const StabilityPair& pair,
                     SimContext& ctx) {
  if (side == StabilitySide::kBefore) {
    ReportTimingViolation(
        std::format("$setuphold violation: data signal {} transitioned inside "
                    "the setup window ending at reference signal {}",
                    pair.data_signal, pair.ref_signal),
        "31.3.3", pair.armed.Entry().loc, ctx);
    return;
  }
  ReportTimingViolation(
      std::format("$setuphold violation: data signal {} transitioned inside "
                  "the hold window beginning at reference signal {}",
                  pair.data_signal, pair.ref_signal),
      "31.3.3", pair.armed.Entry().loc, ctx);
}

void ReportRecrem(StabilitySide side, const StabilityPair& pair,
                  SimContext& ctx) {
  if (side == StabilitySide::kBefore) {
    ReportTimingViolation(
        std::format("$recrem violation: data signal {} transitioned inside the "
                    "removal window ending at reference signal {}",
                    pair.data_signal, pair.ref_signal),
        "31.3.6", pair.armed.Entry().loc, ctx);
    return;
  }
  ReportTimingViolation(
      std::format("$recrem violation: data signal {} transitioned inside the "
                  "recovery window beginning at reference signal {}",
                  pair.data_signal, pair.ref_signal),
      "31.3.6", pair.armed.Entry().loc, ctx);
}

void ReportViolation(TimingCheckKind kind, StabilitySide side,
                     const StabilityPair& pair, SimContext& ctx) {
  if (kind == TimingCheckKind::kSetuphold) {
    ReportSetuphold(side, pair, ctx);
    return;
  }
  if (kind == TimingCheckKind::kRecrem) {
    ReportRecrem(side, pair, ctx);
    return;
  }
  if (kind == TimingCheckKind::kRemoval) {
    ReportTimingViolation(
        std::format("$removal violation: data signal {} transitioned inside "
                    "the window ending at reference signal {}",
                    pair.data_signal, pair.ref_signal),
        "31.3.4", pair.armed.Entry().loc, ctx);
    return;
  }
  ReportTimingViolation(
      std::format("$recovery violation: data signal {} transitioned inside the "
                  "window beginning at reference signal {}",
                  pair.data_signal, pair.ref_signal),
      "31.3.5", pair.armed.Entry().loc, ctx);
}

bool ConditionsAdmit(StabilitySide side, const StabilityPair& pair) {
  const EventConditions& first = side == StabilitySide::kBefore
                                     ? pair.data_conditions
                                     : pair.ref_conditions;
  const EventConditions& second = side == StabilitySide::kBefore
                                      ? pair.ref_conditions
                                      : pair.data_conditions;
  return first.timestamp && second.timecheck;
}

uint64_t DelayedDetectionTicks(const StabilityPair& pair) {
  const SpecifyManager& mgr = *pair.armed.mgr;
  return std::max(
      pair.ref_ticks + mgr.TimingCheckSignalDelay(pair.ref_signal),
      pair.data_ticks + mgr.TimingCheckSignalDelay(pair.data_signal));
}

void EvaluateStabilityPair(const StabilityPair& pair, SimContext& ctx) {
  if (!pair.has_ref || !pair.has_data) return;
  const TimingCheckEntry& check = pair.armed.Entry();
  StabilitySide side =
      ViolatedSide(*pair.armed.mgr, check, pair.ref_ticks, pair.data_ticks);
  if (side == StabilitySide::kNone) return;
  if (!ConditionsAdmit(side, pair)) return;
  const uint64_t kDetected = DelayedDetectionTicks(pair);
  if (check.negative_timing_check_enabled &&
      kDetected > ctx.CurrentTime().ticks) {
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    event->callback = [pair, side, &ctx]() {
      ReportViolation(pair.armed.Entry().kind, side, pair, ctx);
      NoteViolation(pair.armed.Entry(), ctx);
    };
    ctx.GetScheduler().ScheduleEvent(SimTime{kDetected}, Region::kActive,
                                     event);
    return;
  }
  ReportViolation(check.kind, side, pair, ctx);
  NoteViolation(check, ctx);
}

}  // namespace

void ArmStabilityPair(const SpecifyManager& mgr, std::size_t index,
                      SimContext& ctx) {
  auto pair = std::make_shared<StabilityPair>();
  pair->armed = ArmedCheck{&mgr, index};
  const TimingCheckKind kKind = mgr.GetTimingChecks()[index].kind;
  const bool kRefCloses = ClosesWindow(kKind, StabilityEvent::kReference);
  const bool kDataCloses = ClosesWindow(kKind, StabilityEvent::kData);
  ArmedTimingCheckEvents events = ArmTimingCheckEvents(
      pair->armed, ctx,
      [pair, kRefCloses, &ctx]() {
        pair->has_ref = true;
        pair->ref_ticks = ctx.CurrentTime().ticks;
        pair->ref_conditions = ConditionsNow(pair->armed.Entry(), ctx);
        if (!kRefCloses) return;
        ScheduleTimingCheckEvaluation(pair->pending, ctx, [pair, &ctx]() {
          EvaluateStabilityPair(*pair, ctx);
        });
      },
      [pair, kDataCloses, &ctx]() {
        pair->has_data = true;
        pair->data_ticks = ctx.CurrentTime().ticks;
        pair->data_conditions = ConditionsNow(pair->armed.Entry(), ctx);
        if (!kDataCloses) return;
        ScheduleTimingCheckEvaluation(pair->pending, ctx, [pair, &ctx]() {
          EvaluateStabilityPair(*pair, ctx);
        });
      });
  pair->ref_signal = std::move(events.ref_signal);
  pair->data_signal = std::move(events.data_signal);
}

}  // namespace delta
