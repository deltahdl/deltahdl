#include <gtest/gtest.h>

#include <cstdint>
#include <functional>
#include <vector>

#include "common/arena.h"
#include "simulator/dpi_runtime.h"
#include "simulator/scheduler.h"

using namespace delta;

namespace {

// §35.5.1.5 Reentrancy of imported tasks.
//
// This subclause is the counterpart of §35.5.1.1: where an imported *function*
// completes instantly and consumes zero simulation time, an imported *task*
// CAN suspend the currently executing thread. The text states that this
// suspension occurs when an imported task calls an exported task and the
// exported task executes a delay control, event control, or wait statement;
// consequently the imported task's foreign code can be simultaneously active in
// multiple execution threads. (The further requirement that the C programmer
// make standard reentrancy considerations — static variables, thread-safe libc
// — is a foreign-side responsibility a SystemVerilog tool cannot verify, so it
// is not exercised here.)
//
// No new production code is needed: the capability is already realized by two
// existing components acting together.
//   * The Scheduler is the authority on thread suspension and the advance of
//     simulation time. A timing control defers a thread's continuation to a
//     later time slot — modeled here by scheduling a resume event.
//   * DpiRuntime::CallExportFromImport already permits an imported *task* to
//     call an exported task (it returns kOk), and its §35.8 is_task gate
//     guarantees the suspension point is a task: an imported *function* calling
//     an exported task is rejected, so a function can never reach a suspension
//     point. That gate is why §35.5.1.5 speaks specifically of imported tasks.
// These tests drive those production components and observe the suspension,
// the timing-control trigger, and the reentrancy the subclause describes.

constexpr uint64_t kCallTime = 100;
constexpr uint64_t kResumeDelay = 50;

// Build a runtime with one exported task. Its body models a timing control by
// scheduling a resume event `delay` ticks in the future on `sched` and then
// returning — exactly how a delay/event/wait control manifests in this
// scheduler: the thread's continuation is deferred to a later time slot. The
// optional `on_resume` runs when that future slot executes.
DpiRuntime MakeRuntimeWithSuspendingExport(
    Scheduler& sched, uint64_t delay, const std::function<void()>& on_resume) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_wait";
  exp.sv_name = "exported_wait";
  exp.is_task = true;
  exp.impl = [&sched, delay,
              on_resume](const std::vector<DpiArgValue>&) -> DpiArgValue {
    Event* resume = sched.GetEventPool().Acquire();
    resume->callback = [on_resume]() {
      if (on_resume) on_resume();
    };
    sched.ScheduleEvent({sched.CurrentTime().ticks + delay}, Region::kActive,
                        resume);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterExport(std::move(exp));
  return rt;
}

// R1 + R2: an imported task call routed through an exported task that performs
// a timing control suspends the currently executing thread — it defers work to
// a later time slot and the simulation clock advances. This is the dual of
// §35.5.1.1, where an imported function deferred nothing and the clock stood
// still.
TEST(DpiReentrancy,
     ImportedTaskCallThroughExportedTaskSuspendsAndConsumesTime) {
  Arena arena;
  Scheduler sched(arena);
  bool resumed = false;
  uint64_t resume_time = 0;
  DpiRuntime rt = MakeRuntimeWithSuspendingExport(sched, kResumeDelay, [&]() {
    resumed = true;
    resume_time = sched.CurrentTime().ticks;
  });

  bool had_future_work_after_call = false;
  uint64_t horizon_after_call = 0;
  DpiExportCallStatus status = DpiExportCallStatus::kNoncontextChain;

  Event* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    // The importing subroutine is a task, so it is allowed to call an exported
    // task; the chain frame records is_task = true.
    rt.EnterContextImportCall("imported_task", DpiScope{}, /*is_task=*/true);
    DpiArgValue result;
    status = rt.CallExportFromImport("exported_wait", {}, &result);
    rt.LeaveImportCall();
    // The exported task executed its timing control, deferring the thread's
    // continuation to a future time slot: there is now future work pending and
    // the next-event horizon has moved past the current time.
    had_future_work_after_call = sched.HasEvents();
    horizon_after_call = sched.NextEventTime().ticks;
  };
  sched.ScheduleEvent({kCallTime}, Region::kActive, ev);
  sched.Run();

  // The imported-task -> exported-task call was permitted...
  EXPECT_EQ(status, DpiExportCallStatus::kOk);
  // ...and unlike an imported function it suspended: work was deferred to a
  // later slot and the next-event horizon advanced beyond the call time.
  EXPECT_TRUE(had_future_work_after_call);
  EXPECT_EQ(horizon_after_call, kCallTime + kResumeDelay);
  // Running on resumed the thread in that later slot — the suspension really
  // consumed simulation time.
  EXPECT_TRUE(resumed);
  EXPECT_EQ(resume_time, kCallTime + kResumeDelay);
  EXPECT_EQ(sched.CurrentTime().ticks, kCallTime + kResumeDelay);
}

// R3: because the call suspends rather than completing instantly, the imported
// task's foreign code can be simultaneously active in more than one execution
// thread. Two activations of the same imported task are started in different
// time slots; the first is still suspended (awaiting its resume) when the
// second begins, so both are concurrently in flight. A shared activation count
// — the analog of the static variable the subclause warns about — reaches two.
TEST(DpiReentrancy, ImportedTaskCodeSimultaneouslyActiveInMultipleThreads) {
  Arena arena;
  Scheduler sched(arena);

  int active = 0;
  int max_active = 0;
  DpiRuntime rt = MakeRuntimeWithSuspendingExport(sched, kResumeDelay, [&]() {
    // The activation resumes and finishes, leaving the foreign code.
    --active;
  });

  // One activation of the imported task: it enters its foreign code (becoming
  // active), then calls the exported task, which suspends it until a later
  // slot.
  auto start_activation = [&]() {
    ++active;
    if (active > max_active) max_active = active;
    rt.EnterContextImportCall("imported_task", DpiScope{}, /*is_task=*/true);
    DpiArgValue result;
    EXPECT_EQ(rt.CallExportFromImport("exported_wait", {}, &result),
              DpiExportCallStatus::kOk);
    rt.LeaveImportCall();
  };

  // Activation 1 starts at t=100 and suspends until t=150.
  Event* a1 = sched.GetEventPool().Acquire();
  a1->callback = [&]() { start_activation(); };
  sched.ScheduleEvent({kCallTime}, Region::kActive, a1);

  // Activation 2 starts at t=120, while activation 1 is still suspended.
  Event* a2 = sched.GetEventPool().Acquire();
  a2->callback = [&]() { start_activation(); };
  sched.ScheduleEvent({kCallTime + 20}, Region::kActive, a2);

  sched.Run();

  // Both activations of the same imported task were active at once: the foreign
  // code was reentered before the first activation had returned.
  EXPECT_EQ(max_active, 2);
  // Both eventually resumed and left the foreign code.
  EXPECT_EQ(active, 0);
}

// Edge of R2: the suspension is specifically a consequence of the exported task
// executing a timing control — not of the call merely being a task. An exported
// task that performs no timing control (schedules no future continuation)
// returns within the same time slot, so the imported task call does not suspend
// and the clock does not move.
TEST(DpiReentrancy, ImportedTaskCallWithoutTimingControlDoesNotSuspend) {
  Arena arena;
  Scheduler sched(arena);
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_pure_compute";
  exp.sv_name = "exported_compute";
  exp.is_task = true;
  // No timing control: the body just computes and returns in the same slot.
  exp.impl = [](const std::vector<DpiArgValue>& a) -> DpiArgValue {
    return DpiArgValue::FromInt(a.empty() ? 0 : a[0].AsInt() + 1);
  };
  rt.RegisterExport(std::move(exp));

  uint64_t time_before = 0;
  uint64_t time_after = 0;
  bool pending_after = true;
  int32_t result_val = -1;

  Event* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    time_before = sched.CurrentTime().ticks;
    rt.EnterContextImportCall("imported_task", DpiScope{}, /*is_task=*/true);
    DpiArgValue result;
    EXPECT_EQ(rt.CallExportFromImport("exported_compute",
                                      {DpiArgValue::FromInt(41)}, &result),
              DpiExportCallStatus::kOk);
    rt.LeaveImportCall();
    result_val = result.AsInt();
    time_after = sched.CurrentTime().ticks;
    // No timing control ran, so nothing was deferred to a *future* slot. The
    // discriminating query is NextEventTime(), not HasEvents(): the event
    // calendar still holds the current in-progress slot (Run() erases it only
    // after the slot finishes executing), so HasEvents() is trivially true
    // inside any callback. NextEventTime() reports only future work
    // (upper_bound(current_time_), scheduler.h), which is what "deferred to a
    // future slot" means and what the suspending sibling test observes advance.
    pending_after = sched.NextEventTime().ticks > sched.CurrentTime().ticks;
  };
  sched.ScheduleEvent({kCallTime}, Region::kActive, ev);
  sched.Run();

  EXPECT_EQ(result_val, 42);
  EXPECT_EQ(time_before, kCallTime);
  EXPECT_EQ(time_after, kCallTime);
  EXPECT_FALSE(pending_after);
  EXPECT_EQ(sched.CurrentTime().ticks, kCallTime);
}

}  // namespace
