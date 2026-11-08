#include <gtest/gtest.h>

#include <cstdint>
#include <functional>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/scheduler.h"

using namespace delta;

namespace {

constexpr uint64_t kCallTime = 100;
constexpr uint64_t kResumeDelay = 50;

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
    rt.EnterContextImportCall("imported_task", DpiScope{}, true);
    DpiArgValue result;
    status = rt.CallExportFromImport("exported_wait", {}, &result);
    rt.LeaveImportCall();
    had_future_work_after_call = sched.HasEvents();
    horizon_after_call = sched.NextEventTime().ticks;
  };
  sched.ScheduleEvent({kCallTime}, Region::kActive, ev);
  sched.Run();

  EXPECT_EQ(status, DpiExportCallStatus::kOk);
  EXPECT_TRUE(had_future_work_after_call);
  EXPECT_EQ(horizon_after_call, kCallTime + kResumeDelay);
  EXPECT_TRUE(resumed);
  EXPECT_EQ(resume_time, kCallTime + kResumeDelay);
  EXPECT_EQ(sched.CurrentTime().ticks, kCallTime + kResumeDelay);
}

TEST(DpiReentrancy, ImportedTaskCodeSimultaneouslyActiveInMultipleThreads) {
  Arena arena;
  Scheduler sched(arena);

  int active = 0;
  int max_active = 0;
  DpiRuntime rt =
      MakeRuntimeWithSuspendingExport(sched, kResumeDelay, [&]() { --active; });

  auto start_activation = [&]() {
    ++active;
    if (active > max_active) max_active = active;
    rt.EnterContextImportCall("imported_task", DpiScope{}, true);
    DpiArgValue result;
    EXPECT_EQ(rt.CallExportFromImport("exported_wait", {}, &result),
              DpiExportCallStatus::kOk);
    rt.LeaveImportCall();
  };

  Event* a1 = sched.GetEventPool().Acquire();
  a1->callback = [&]() { start_activation(); };
  sched.ScheduleEvent({kCallTime}, Region::kActive, a1);

  Event* a2 = sched.GetEventPool().Acquire();
  a2->callback = [&]() { start_activation(); };
  sched.ScheduleEvent({kCallTime + 20}, Region::kActive, a2);

  sched.Run();

  EXPECT_EQ(max_active, 2);
  EXPECT_EQ(active, 0);
}

TEST(DpiReentrancy, ImportedTaskCallWithoutTimingControlDoesNotSuspend) {
  Arena arena;
  Scheduler sched(arena);
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_pure_compute";
  exp.sv_name = "exported_compute";
  exp.is_task = true;
  int32_t computed = -1;
  exp.impl = [&computed](const std::vector<DpiArgValue>& a) -> DpiArgValue {
    computed = a.empty() ? 0 : a[0].AsInt() + 1;
    return DpiArgValue::FromInt(computed);
  };
  rt.RegisterExport(std::move(exp));

  uint64_t time_before = 0;
  uint64_t time_after = 0;
  bool pending_after = true;
  int32_t result_val = -1;

  Event* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    time_before = sched.CurrentTime().ticks;
    rt.EnterContextImportCall("imported_task", DpiScope{}, true);
    DpiArgValue result;
    EXPECT_EQ(rt.CallExportFromImport("exported_compute",
                                      {DpiArgValue::FromInt(41)}, &result),
              DpiExportCallStatus::kOk);
    rt.LeaveImportCall();
    result_val = result.AsInt();
    time_after = sched.CurrentTime().ticks;
    pending_after = sched.NextEventTime().ticks > sched.CurrentTime().ticks;
  };
  sched.ScheduleEvent({kCallTime}, Region::kActive, ev);
  sched.Run();

  EXPECT_EQ(computed, 42);
  EXPECT_EQ(result_val, 0);
  EXPECT_EQ(time_before, kCallTime);
  EXPECT_EQ(time_after, kCallTime);
  EXPECT_FALSE(pending_after);
  EXPECT_EQ(sched.CurrentTime().ticks, kCallTime);
}

}  // namespace
