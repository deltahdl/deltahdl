#include "simulator/timing_check_skew.h"

#include <cstddef>
#include <cstdint>
#include <format>
#include <functional>
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

struct SkewWindow {
  ArmedCheck armed;
  std::string ref_signal;
  std::string data_signal;
  bool open = false;
  bool ref_is_timestamp = true;
  uint64_t timestamp_ticks = 0;
  std::shared_ptr<bool> timeout_cancelled;

  bool ref_moved = false;
  bool ref_suppressed = false;
  bool data_moved = false;
  std::shared_ptr<bool> pending = std::make_shared<bool>(false);
};

uint64_t WindowLimit(const TimingCheckEntry& check, bool ref_is_timestamp) {
  return ref_is_timestamp ? check.limit : check.limit2;
}

void ReportSkewViolation(const SkewWindow& window, uint64_t limit,
                         SimContext& ctx) {
  const TimingCheckEntry& check = window.armed.Entry();
  if (window.armed.mgr->GetTimingCheckInvocationOptions()
          .all_timing_checks_off) {
    return;
  }
  if (check.kind == TimingCheckKind::kFullskew) {
    ReportTimingViolation(
        std::format("$fullskew violation: signals {} and {} moved more than "
                    "the {} time units the check allows apart",
                    window.ref_signal, window.data_signal, limit),
        "31.4.3", check.loc, ctx);
  } else if (check.kind == TimingCheckKind::kSkew) {
    ReportTimingViolation(
        std::format("$skew violation: data signal {} followed reference signal "
                    "{} by more than the {} time units the check allows",
                    window.data_signal, window.ref_signal, limit),
        "31.4.1", check.loc, ctx);
  } else {
    ReportTimingViolation(
        std::format("$timeskew violation: data signal {} did not follow "
                    "reference signal {} within the {} time units the check "
                    "allows",
                    window.data_signal, window.ref_signal, limit),
        "31.4.2", check.loc, ctx);
  }
  NoteViolation(check, ctx);
}

void CancelTimeout(SkewWindow& window) {
  if (window.timeout_cancelled != nullptr) *window.timeout_cancelled = true;
  window.timeout_cancelled = nullptr;
}

void CloseWindow(SkewWindow& window) {
  window.open = false;
  CancelTimeout(window);
}

void ArmTimeout(const std::shared_ptr<SkewWindow>& window, SimContext& ctx) {
  const uint64_t kLimit =
      WindowLimit(window->armed.Entry(), window->ref_is_timestamp);
  auto cancelled = std::make_shared<bool>(false);
  window->timeout_cancelled = cancelled;
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->superseded = cancelled;
  event->callback = [window, cancelled, kLimit, &ctx]() {
    if (*cancelled || !window->open) return;
    CloseWindow(*window);
    ReportSkewViolation(*window, kLimit, ctx);
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime() + SimTime{kLimit},
                                   Region::kPrePostponed, event);
}

void OnTimestampEvent(const std::shared_ptr<SkewWindow>& window, bool ref_moved,
                      SimContext& ctx) {
  CancelTimeout(*window);
  window->open = true;
  window->ref_is_timestamp = ref_moved;
  window->timestamp_ticks = ctx.CurrentTime().ticks;
  const TimingCheckEntry& check = window->armed.Entry();
  if (check.kind == TimingCheckKind::kSkew) return;
  if (check.event_based_flag) return;
  ArmTimeout(window, ctx);
}

bool OnSkewDataEvent(SkewWindow& window, SimContext& ctx) {
  if (!window.open) return false;
  const uint64_t kNow = ctx.CurrentTime().ticks;
  if (kNow <= window.timestamp_ticks) return false;
  const TimingCheckEntry& check = window.armed.Entry();
  if (kNow - window.timestamp_ticks <= check.limit) return false;
  ReportSkewViolation(window, check.limit, ctx);
  return true;
}

void OnTimeskewDataEvent(SkewWindow& window, SimContext& ctx) {
  const TimingCheckEntry& check = window.armed.Entry();
  if (!check.event_based_flag) {
    CloseWindow(window);
    return;
  }
  if (OnSkewDataEvent(window, ctx) && !check.remain_active_flag) {
    CloseWindow(window);
  }
}

void OnFullskewEvent(const std::shared_ptr<SkewWindow>& window, bool ref_moved,
                     SimContext& ctx) {
  const bool kIsTimecheck =
      window->open && window->ref_is_timestamp != ref_moved;
  if (!kIsTimecheck) {
    OnTimestampEvent(window, ref_moved, ctx);
    return;
  }
  const TimingCheckEntry& check = window->armed.Entry();
  if (!check.event_based_flag) {
    CloseWindow(*window);
    return;
  }
  const uint64_t kNow = ctx.CurrentTime().ticks;
  const uint64_t kLimit = WindowLimit(check, window->ref_is_timestamp);
  const bool kAfterLimit =
      kNow > window->timestamp_ticks && kNow - window->timestamp_ticks > kLimit;
  if (!kAfterLimit) {
    CloseWindow(*window);
    return;
  }
  ReportSkewViolation(*window, kLimit, ctx);
  OnTimestampEvent(window, ref_moved, ctx);
}

void OnSuppressedRefEdge(const std::shared_ptr<SkewWindow>& window) {
  if (window->armed.Entry().remain_active_flag) return;
  CloseWindow(*window);
}

void OnRefEdge(const std::shared_ptr<SkewWindow>& window, SimContext& ctx) {
  if (window->armed.Entry().kind == TimingCheckKind::kFullskew) {
    OnFullskewEvent(window, true, ctx);
    return;
  }
  OnTimestampEvent(window, true, ctx);
}

void OnDataEdge(const std::shared_ptr<SkewWindow>& window, SimContext& ctx) {
  const TimingCheckKind kKind = window->armed.Entry().kind;
  if (kKind == TimingCheckKind::kFullskew) {
    OnFullskewEvent(window, false, ctx);
    return;
  }
  if (kKind == TimingCheckKind::kSkew) {
    OnSkewDataEvent(*window, ctx);
    return;
  }
  OnTimeskewDataEvent(*window, ctx);
}

void ApplySlotEvents(const std::shared_ptr<SkewWindow>& window,
                     SimContext& ctx) {
  const bool kRefMoved = window->ref_moved;
  const bool kRefSuppressed = window->ref_suppressed;
  const bool kDataMoved = window->data_moved;
  window->ref_moved = false;
  window->ref_suppressed = false;
  window->data_moved = false;
  if (kRefMoved) {
    OnRefEdge(window, ctx);
  } else if (kRefSuppressed) {
    OnSuppressedRefEdge(window);
  }
  if (kDataMoved) OnDataEdge(window, ctx);
}

}  // namespace

void ArmSkewWindow(const SpecifyManager& mgr, std::size_t index,
                   SimContext& ctx) {
  auto window = std::make_shared<SkewWindow>();
  window->armed = ArmedCheck{&mgr, index};
  const bool kSuppressedRefActs =
      mgr.GetTimingChecks()[index].kind != TimingCheckKind::kSkew;
  ArmedTimingCheckEvents events = ArmTimingCheckEvents(
      window->armed, ctx,
      [window, &ctx]() {
        CancelTimeout(*window);
        window->ref_moved = true;
        ScheduleTimingCheckEvaluation(window->pending, ctx, [window, &ctx]() {
          ApplySlotEvents(window, ctx);
        });
      },
      [window, &ctx]() {
        CancelTimeout(*window);
        window->data_moved = true;
        ScheduleTimingCheckEvaluation(window->pending, ctx, [window, &ctx]() {
          ApplySlotEvents(window, ctx);
        });
      },
      kSuppressedRefActs ? std::function<void()>([window, &ctx]() {
        window->ref_suppressed = true;
        ScheduleTimingCheckEvaluation(window->pending, ctx, [window, &ctx]() {
          ApplySlotEvents(window, ctx);
        });
      })
                         : std::function<void()>());
  window->ref_signal = std::move(events.ref_signal);
  window->data_signal = std::move(events.data_signal);
}

}  // namespace delta
