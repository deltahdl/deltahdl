#include "simulator/timing_check_driver.h"

#include <cstddef>
#include <cstdint>
#include <format>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "parser/ast_specify.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"
#include "simulator/timing_check_driver_internal.h"
#include "simulator/timing_check_pulse.h"
#include "simulator/timing_check_skew.h"
#include "simulator/timing_check_stability.h"
#include "simulator/variable.h"

namespace delta {
namespace {

bool SetupWindowViolated(uint64_t limit, uint64_t timestamp_ticks,
                         uint64_t timecheck_ticks) {
  return timestamp_ticks < timecheck_ticks &&
         timecheck_ticks - timestamp_ticks < limit;
}

bool HoldWindowViolated(uint64_t limit, uint64_t timestamp_ticks,
                        uint64_t timecheck_ticks) {
  return timecheck_ticks >= timestamp_ticks &&
         timecheck_ticks - timestamp_ticks < limit;
}

struct StabilityWindowEvents {
  std::string timestamp_signal;
  TimingCheckEdge timestamp_edge;
  std::string timecheck_signal;
  TimingCheckEdge timecheck_edge;
};

StabilityWindowEvents EventsOf(const TimingCheckEntry& check) {
  if (check.kind == TimingCheckKind::kSetup) {
    return StabilityWindowEvents{
        check.inst_prefix + check.data_signal, DataEdgeOf(check),
        check.inst_prefix + check.ref_signal, RefEdgeOf(check)};
  }
  return StabilityWindowEvents{
      check.inst_prefix + check.ref_signal, RefEdgeOf(check),
      check.inst_prefix + check.data_signal, DataEdgeOf(check)};
}

struct StabilityWindow {
  ArmedCheck armed;
  StabilityWindowEvents events;
  bool has_timestamp = false;
  uint64_t timestamp_ticks = 0;

  uint64_t timecheck_ticks = 0;
  std::shared_ptr<bool> pending = std::make_shared<bool>(false);
};

void ReportViolation(TimingCheckKind kind, const StabilityWindow& window,
                     SimContext& ctx) {
  if (kind == TimingCheckKind::kSetup) {
    ReportTimingViolation(
        std::format("$setup violation: data signal {} transitioned inside the "
                    "window ending at reference signal {}",
                    window.events.timestamp_signal,
                    window.events.timecheck_signal),
        "31.3.1", window.armed.Entry().loc, ctx);
    return;
  }
  ReportTimingViolation(
      std::format("$hold violation: data signal {} transitioned inside the "
                  "window beginning at reference signal {}",
                  window.events.timecheck_signal,
                  window.events.timestamp_signal),
      "31.3.2", window.armed.Entry().loc, ctx);
}

void EvaluateStabilityWindow(const StabilityWindow& window,
                             uint64_t timecheck_ticks, SimContext& ctx) {
  if (!window.has_timestamp) return;
  const TimingCheckEntry& check = window.armed.Entry();
  bool violated = check.kind == TimingCheckKind::kSetup
                      ? SetupWindowViolated(check.limit, window.timestamp_ticks,
                                            timecheck_ticks)
                      : HoldWindowViolated(check.limit, window.timestamp_ticks,
                                           timecheck_ticks);
  if (!violated) return;
  ReportViolation(check.kind, window, ctx);
  NoteViolation(check, ctx);
}

void ArmStabilityWindow(const SpecifyManager& mgr, std::size_t index,
                        SimContext& ctx) {
  const TimingCheckEntry& check = mgr.GetTimingChecks()[index];
  bool is_setup = check.kind == TimingCheckKind::kSetup;
  StabilityWindowEvents events = EventsOf(check);
  Variable* timestamp_var = ctx.FindVariable(events.timestamp_signal);
  Variable* timecheck_var = ctx.FindVariable(events.timecheck_signal);
  if (timestamp_var == nullptr || timecheck_var == nullptr) return;
  TimingCheckEdge timestamp_edge = events.timestamp_edge;
  TimingCheckEdge timecheck_edge = events.timecheck_edge;
  auto window = std::make_shared<StabilityWindow>();
  window->armed = ArmedCheck{&mgr, index};
  window->events = std::move(events);
  WatchConditionedEdge(timestamp_var, std::move(timestamp_edge),
                       ConditionedEvent{window->armed, is_setup}, ctx,
                       {[window, &ctx]() {
                          window->has_timestamp = true;
                          window->timestamp_ticks = ctx.CurrentTime().ticks;
                        },
                        nullptr});
  WatchConditionedEdge(
      timecheck_var, std::move(timecheck_edge),
      ConditionedEvent{window->armed, !is_setup}, ctx,
      {[window, &ctx]() {
         window->timecheck_ticks = ctx.CurrentTime().ticks;
         ScheduleTimingCheckEvaluation(window->pending, ctx, [window, &ctx]() {
           EvaluateStabilityWindow(*window, window->timecheck_ticks, ctx);
         });
       },
       nullptr});
}

}  // namespace

void WatchTimingChecks(const SpecifyManager& mgr, SimContext& ctx) {
  const std::vector<TimingCheckEntry>& checks = mgr.GetTimingChecks();
  for (std::size_t i = 0; i < checks.size(); ++i) {
    switch (checks[i].kind) {
      case TimingCheckKind::kSetup:
      case TimingCheckKind::kHold:
        ArmStabilityWindow(mgr, i, ctx);
        break;
      case TimingCheckKind::kSetuphold:
      case TimingCheckKind::kRecovery:
      case TimingCheckKind::kRemoval:
      case TimingCheckKind::kRecrem:
        ArmStabilityPair(mgr, i, ctx);
        break;
      case TimingCheckKind::kWidth:
      case TimingCheckKind::kPeriod:
      case TimingCheckKind::kNochange:
        ArmPulseWindow(mgr, i, ctx);
        break;
      case TimingCheckKind::kSkew:
      case TimingCheckKind::kTimeskew:
      case TimingCheckKind::kFullskew:
        ArmSkewWindow(mgr, i, ctx);
        break;
    }
  }
}

}  // namespace delta
