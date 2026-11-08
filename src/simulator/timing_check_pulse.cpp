#include "simulator/timing_check_pulse.h"

#include <cstddef>
#include <cstdint>
#include <format>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_specify.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"
#include "simulator/timing_check_driver_internal.h"
#include "simulator/variable.h"

namespace delta {
namespace {

bool AllTimingChecksOff(const ArmedCheck& armed) {
  return armed.mgr->GetTimingCheckInvocationOptions().all_timing_checks_off;
}

TimingCheckEdge OppositeEdge(const TimingCheckEdge& edge) {
  if (!edge.descriptors.empty()) {
    TimingCheckEdge opposite;
    opposite.edge = edge.edge;
    opposite.select = edge.select;
    opposite.descriptors.reserve(edge.descriptors.size());
    for (const std::pair<char, char>& descriptor : edge.descriptors) {
      opposite.descriptors.emplace_back(descriptor.second, descriptor.first);
    }
    return opposite;
  }
  if (edge.edge == SpecifyEdge::kPosedge) {
    return TimingCheckEdge{SpecifyEdge::kNegedge, {}, edge.select};
  }
  if (edge.edge == SpecifyEdge::kNegedge) {
    return TimingCheckEdge{SpecifyEdge::kPosedge, {}, edge.select};
  }
  return edge;
}

bool WidthPulseViolated(const TimingCheckEntry& check, uint64_t elapsed) {
  return elapsed > check.threshold && elapsed < check.limit;
}

bool PeriodViolated(const TimingCheckEntry& check, uint64_t elapsed) {
  return elapsed < check.limit;
}

struct PulseWindow {
  ArmedCheck armed;
  std::string signal;
  bool has_timestamp = false;
  uint64_t timestamp_ticks = 0;
};

void ReportPulseViolation(const TimingCheckEntry& check,
                          const std::string& signal, uint64_t elapsed,
                          SimContext& ctx) {
  if (check.kind == TimingCheckKind::kWidth) {
    ReportTimingViolation(
        std::format("$width violation: signal {} held its level for {} time "
                    "units, short of the {} the check requires",
                    signal, elapsed, check.limit),
        "31.4.4", check.loc, ctx);
    return;
  }
  ReportTimingViolation(
      std::format("$period violation: signal {} repeated its edge after {} "
                  "time units, short of the {} the check requires",
                  signal, elapsed, check.limit),
      "31.4.5", check.loc, ctx);
}

void EvaluatePulseWindow(const PulseWindow& window, uint64_t timecheck_ticks,
                         SimContext& ctx) {
  if (!window.has_timestamp) return;
  if (timecheck_ticks <= window.timestamp_ticks) return;
  if (AllTimingChecksOff(window.armed)) return;
  const TimingCheckEntry& check = window.armed.Entry();
  uint64_t elapsed = timecheck_ticks - window.timestamp_ticks;
  bool violated = check.kind == TimingCheckKind::kWidth
                      ? WidthPulseViolated(check, elapsed)
                      : PeriodViolated(check, elapsed);
  if (!violated) return;
  ReportPulseViolation(check, window.signal, elapsed, ctx);
  NoteViolation(check, ctx);
}

void ArmWidthWindow(const SpecifyManager& mgr, std::size_t index,
                    SimContext& ctx) {
  const TimingCheckEntry& check = mgr.GetTimingChecks()[index];
  std::string signal = check.inst_prefix + check.ref_signal;
  Variable* var = ctx.FindVariable(signal);
  if (var == nullptr) return;
  TimingCheckEdge opening_edge = RefEdgeOf(check);
  auto window = std::make_shared<PulseWindow>();
  window->armed = ArmedCheck{&mgr, index};
  window->signal = std::move(signal);
  ConditionedEvent ref_event{window->armed, false};
  WatchConditionedEdge(var, OppositeEdge(opening_edge), ref_event, ctx,
                       {[window, &ctx]() {
                          EvaluatePulseWindow(*window, ctx.CurrentTime().ticks,
                                              ctx);
                          window->has_timestamp = false;
                        },
                        nullptr});
  WatchConditionedEdge(var, std::move(opening_edge), ref_event, ctx,
                       {[window, &ctx]() {
                          window->has_timestamp = true;
                          window->timestamp_ticks = ctx.CurrentTime().ticks;
                        },
                        nullptr});
}

void ArmPeriodWindow(const SpecifyManager& mgr, std::size_t index,
                     SimContext& ctx) {
  const TimingCheckEntry& check = mgr.GetTimingChecks()[index];
  std::string signal = check.inst_prefix + check.ref_signal;
  Variable* var = ctx.FindVariable(signal);
  if (var == nullptr) return;
  TimingCheckEdge edge = RefEdgeOf(check);
  auto window = std::make_shared<PulseWindow>();
  window->armed = ArmedCheck{&mgr, index};
  window->signal = std::move(signal);
  WatchConditionedEdge(var, std::move(edge),
                       ConditionedEvent{window->armed, false}, ctx,
                       {[window, &ctx]() {
                          uint64_t now = ctx.CurrentTime().ticks;
                          EvaluatePulseWindow(*window, now, ctx);
                          window->has_timestamp = true;
                          window->timestamp_ticks = now;
                        },
                        nullptr});
}

struct NochangeWindow {
  ArmedCheck armed;
  std::string ref_signal;
  std::string data_signal;
  bool has_leading = false;
  uint64_t leading_ticks = 0;
  bool has_trailing = false;
  uint64_t trailing_ticks = 0;
  std::vector<uint64_t> pending;
};

bool NochangeWindowViolated(const TimingCheckEntry& check,
                            uint64_t leading_ticks, uint64_t trailing_ticks,
                            uint64_t data_ticks) {
  int64_t begin = static_cast<int64_t>(leading_ticks) - check.start_edge_offset;
  int64_t end = static_cast<int64_t>(trailing_ticks) + check.end_edge_offset;
  auto data = static_cast<int64_t>(data_ticks);
  return begin < data && data < end;
}

void ReportNochangeViolation(const NochangeWindow& window, SimContext& ctx) {
  if (AllTimingChecksOff(window.armed)) return;
  const TimingCheckEntry& check = window.armed.Entry();
  ReportTimingViolation(
      std::format("$nochange violation: data signal {} transitioned inside "
                  "the window bounded by reference signal {}",
                  window.data_signal, window.ref_signal),
      "31.4.6", check.loc, ctx);
  NoteViolation(check, ctx);
}

void EvaluateNochangeData(const NochangeWindow& window, uint64_t data_ticks,
                          SimContext& ctx) {
  if (NochangeWindowViolated(window.armed.Entry(), window.leading_ticks,
                             window.trailing_ticks, data_ticks)) {
    ReportNochangeViolation(window, ctx);
  }
}

void CloseNochangeWindow(NochangeWindow& window, uint64_t trailing_ticks,
                         SimContext& ctx) {
  if (!window.has_leading) return;
  window.has_trailing = true;
  window.trailing_ticks = trailing_ticks;
  std::vector<uint64_t> held = std::move(window.pending);
  window.pending.clear();
  for (uint64_t data_ticks : held) {
    EvaluateNochangeData(window, data_ticks, ctx);
  }
}

void DropTransitionsBefore(NochangeWindow& window, uint64_t reference_ticks) {
  const TimingCheckEntry& check = window.armed.Entry();
  const int64_t kBegin =
      static_cast<int64_t>(reference_ticks) - check.start_edge_offset;
  std::vector<uint64_t> kept;
  for (uint64_t data_ticks : window.pending) {
    if (static_cast<int64_t>(data_ticks) > kBegin) kept.push_back(data_ticks);
  }
  window.pending = std::move(kept);
}

void SettleOpenNochangeWindow(NochangeWindow& window, uint64_t now,
                              SimContext& ctx) {
  if (!window.has_leading || window.has_trailing) return;
  std::vector<uint64_t> kept;
  std::vector<uint64_t> settled;
  for (uint64_t data_ticks : window.pending) {
    (data_ticks == now ? settled : kept).push_back(data_ticks);
  }
  window.pending = std::move(kept);
  for (std::size_t i = 0; i < settled.size(); ++i) {
    ReportNochangeViolation(window, ctx);
  }
}

bool AnswerInOpenWindow(const std::shared_ptr<NochangeWindow>& shared,
                        uint64_t data_ticks, SimContext& ctx) {
  NochangeWindow& window = *shared;
  const TimingCheckEntry& check = window.armed.Entry();
  const int64_t kBegin =
      static_cast<int64_t>(window.leading_ticks) - check.start_edge_offset;
  if (static_cast<int64_t>(data_ticks) <= kBegin) return false;
  if (check.end_edge_offset > 0) {
    ReportNochangeViolation(window, ctx);
    return true;
  }
  if (check.end_edge_offset < 0) return false;
  window.pending.push_back(data_ticks);
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [shared, data_ticks, &ctx]() {
    SettleOpenNochangeWindow(*shared, data_ticks, ctx);
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kInactive, event);
  return true;
}

void RecordNochangeData(const std::shared_ptr<NochangeWindow>& shared,
                        uint64_t data_ticks, SimContext& ctx) {
  NochangeWindow& window = *shared;
  if (window.has_leading && window.has_trailing) {
    EvaluateNochangeData(window, data_ticks, ctx);
  }
  if (window.has_leading && !window.has_trailing &&
      AnswerInOpenWindow(shared, data_ticks, ctx)) {
    return;
  }
  if (!window.has_leading || window.has_trailing) {
    DropTransitionsBefore(window, data_ticks);
  }
  window.pending.push_back(data_ticks);
}

void ArmNochangeWindow(const SpecifyManager& mgr, std::size_t index,
                       SimContext& ctx) {
  const TimingCheckEntry& check = mgr.GetTimingChecks()[index];
  std::string ref_signal = check.inst_prefix + check.ref_signal;
  std::string data_signal = check.inst_prefix + check.data_signal;
  Variable* ref_var = ctx.FindVariable(ref_signal);
  Variable* data_var = ctx.FindVariable(data_signal);
  if (ref_var == nullptr || data_var == nullptr) return;
  TimingCheckEdge leading_edge = RefEdgeOf(check);
  TimingCheckEdge trailing_edge = OppositeEdge(leading_edge);
  TimingCheckEdge data_edge = DataEdgeOf(check);
  auto window = std::make_shared<NochangeWindow>();
  window->armed = ArmedCheck{&mgr, index};
  window->ref_signal = std::move(ref_signal);
  window->data_signal = std::move(data_signal);
  ConditionedEvent ref_event{window->armed, false};
  ConditionedEvent data_event{window->armed, true};
  WatchConditionedEdge(ref_var, std::move(leading_edge), ref_event, ctx,
                       {[window, &ctx]() {
                          window->has_leading = true;
                          window->has_trailing = false;
                          window->leading_ticks = ctx.CurrentTime().ticks;
                          DropTransitionsBefore(*window, window->leading_ticks);
                        },
                        nullptr});
  WatchConditionedEdge(ref_var, std::move(trailing_edge), ref_event, ctx,
                       {[window, &ctx]() {
                          CloseNochangeWindow(*window, ctx.CurrentTime().ticks,
                                              ctx);
                        },
                        nullptr});
  WatchConditionedEdge(data_var, std::move(data_edge), data_event, ctx,
                       {[window, &ctx]() {
                          RecordNochangeData(window, ctx.CurrentTime().ticks,
                                             ctx);
                        },
                        nullptr});
}

}  // namespace

void ArmPulseWindow(const SpecifyManager& mgr, std::size_t index,
                    SimContext& ctx) {
  TimingCheckKind kind = mgr.GetTimingChecks()[index].kind;
  if (kind == TimingCheckKind::kWidth) {
    ArmWidthWindow(mgr, index, ctx);
    return;
  }
  if (kind == TimingCheckKind::kPeriod) {
    ArmPeriodWindow(mgr, index, ctx);
    return;
  }
  if (kind == TimingCheckKind::kNochange) ArmNochangeWindow(mgr, index, ctx);
}

}  // namespace delta
