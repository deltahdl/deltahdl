#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_dpi_bump_import.h"
#include "helpers_dpi_touch_import.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

DpiRuntime MakeDoublingImport() {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_double";
  func.sv_name = "twice";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    return DpiArgValue::FromInt(a[0].AsInt() * 2);
  };
  rt.RegisterImport(std::move(func));
  return rt;
}

constexpr uint64_t kCallTime = 100;

TEST(DpiInstantCompletion, ImportedFunctionCallLeavesSimulationTimeUnchanged) {
  Arena arena;
  Scheduler sched(arena);
  DpiRuntime rt = MakeDoublingImport();

  uint64_t time_before = 0;
  uint64_t time_after = 0;
  int32_t result = 0;

  Event* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    time_before = sched.CurrentTime().ticks;
    std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(21)};
    result = rt.CallImportWithArgs("twice", actuals).AsInt();
    time_after = sched.CurrentTime().ticks;
  };
  sched.ScheduleEvent({kCallTime}, Region::kActive, ev);
  sched.Run();

  EXPECT_EQ(time_before, kCallTime);
  EXPECT_EQ(result, 42);
  EXPECT_EQ(time_after, kCallTime);
}

TEST(DpiInstantCompletion,
     ImportedFunctionCallSchedulesNoFutureSimulationWork) {
  Arena arena;
  Scheduler sched(arena);
  DpiRuntime rt = MakeDoublingImport();

  size_t scheduled_before = 0;
  size_t scheduled_after = 0;
  uint64_t horizon_after = 0;

  Event* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    scheduled_before = sched.EvaluationEventScheduledCount();
    std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(5)};
    rt.CallImportWithArgs("twice", actuals);
    scheduled_after = sched.EvaluationEventScheduledCount();
    horizon_after = sched.NextEventTime().ticks;
  };
  sched.ScheduleEvent({kCallTime}, Region::kActive, ev);
  sched.Run();

  EXPECT_EQ(scheduled_after, scheduled_before);
  EXPECT_EQ(horizon_after, kCallTime);
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(sched.CurrentTime().ticks, kCallTime);
}

TEST(DpiInstantCompletion, MultipleImportedCallsInOneSlotConsumeZeroTime) {
  Arena arena;
  Scheduler sched(arena);
  DpiRuntime rt = MakeDoublingImport();

  uint64_t time_before = 0;
  uint64_t time_after = 0;
  size_t scheduled_before = 0;
  size_t scheduled_after = 0;
  int32_t last = 0;

  Event* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    time_before = sched.CurrentTime().ticks;
    scheduled_before = sched.EvaluationEventScheduledCount();
    for (int32_t i = 0; i < 5; ++i) {
      std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(i)};
      last = rt.CallImportWithArgs("twice", actuals).AsInt();
    }
    time_after = sched.CurrentTime().ticks;
    scheduled_after = sched.EvaluationEventScheduledCount();
  };
  sched.ScheduleEvent({kCallTime}, Region::kActive, ev);
  sched.Run();

  EXPECT_EQ(time_before, kCallTime);
  EXPECT_EQ(time_after, kCallTime);
  EXPECT_EQ(scheduled_after, scheduled_before);
  EXPECT_EQ(last, 8);
}

TEST(DpiInstantCompletion, ImportedFunctionWithOutputArgConsumesZeroTime) {
  Arena arena;
  Scheduler sched(arena);
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_emit";
  func.sv_name = "emit";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"o", DataTypeKind::kInt, Direction::kOutput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromInt(77);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  uint64_t time_before = 0;
  uint64_t time_after = 0;
  int32_t written = 0;

  Event* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    time_before = sched.CurrentTime().ticks;
    std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(0)};
    rt.CallImportWithArgs("emit", actuals);
    written = actuals[0].AsInt();
    time_after = sched.CurrentTime().ticks;
  };
  sched.ScheduleEvent({kCallTime}, Region::kActive, ev);
  sched.Run();

  EXPECT_EQ(written, 77);
  EXPECT_EQ(time_before, kCallTime);
  EXPECT_EQ(time_after, kCallTime);
}

TEST(DpiInstantCompletion, ChangeDetectingImportCallConsumesZeroTime) {
  Arena arena;
  Scheduler sched(arena);
  DpiRuntime rt;
  RegisterBumpImport(rt);

  uint64_t time_before = 0;
  uint64_t time_after = 0;
  size_t scheduled_before = 0;
  size_t scheduled_after = 0;
  size_t change_count = 0;
  int32_t new_value = 0;

  Event* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    time_before = sched.CurrentTime().ticks;
    scheduled_before = sched.EvaluationEventScheduledCount();
    std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(41)};
    std::vector<DpiArgValueChange> changes;
    rt.CallImportDetectingChanges("bump", actuals, changes);
    change_count = changes.size();
    if (!changes.empty()) new_value = changes[0].new_value.AsInt();
    time_after = sched.CurrentTime().ticks;
    scheduled_after = sched.EvaluationEventScheduledCount();
  };
  sched.ScheduleEvent({kCallTime}, Region::kActive, ev);
  sched.Run();

  EXPECT_EQ(change_count, 1u);
  EXPECT_EQ(new_value, 42);
  EXPECT_EQ(time_before, kCallTime);
  EXPECT_EQ(time_after, kCallTime);
  EXPECT_EQ(scheduled_after, scheduled_before);
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(sched.CurrentTime().ticks, kCallTime);
}

struct CallingFromAnEvent {
  DpiRuntime dpi;
  SimFixture f;
  uint64_t seen = 0;
  uint64_t time_after = 0;
  uint64_t actual_in_slot = 0;

  CallingFromAnEvent(Direction direction, uint64_t wrote) {
    RegisterTouchImport(dpi, direction, wrote, &seen);
    f.ctx.SetDpiRuntime(&dpi);
    f.ctx.CreateVariable("a", 32)->value = MakeLogic4VecVal(f.arena, 32, 5);
    const Expr* call = ParseExprFrom("touch(a)", f);
    Event* ev = f.scheduler.GetEventPool().Acquire();
    ev->callback = [this, call]() {
      EvalFunctionCall(call, f.ctx, f.arena);
      time_after = f.scheduler.CurrentTime().ticks;
      actual_in_slot = f.ctx.FindVariable("a")->value.ToUint64();
    };
    f.scheduler.ScheduleEvent({kCallTime}, Region::kActive, ev);
    f.scheduler.Run();
  }
};

TEST(DpiInstantCompletion, ADesignsImportedCallReturnsAtTheTimeItWasMadeAt) {
  CallingFromAnEvent run(Direction::kInput, 111);
  EXPECT_EQ(run.time_after, kCallTime);
}

TEST(DpiInstantCompletion, ADesignsOutputArgumentIsWrittenInTheCallsOwnSlot) {
  CallingFromAnEvent run(Direction::kOutput, 77);
  EXPECT_EQ(run.actual_in_slot, 77U);
}

TEST(DpiInstantCompletion, ADesignsImportedCallDefersNothingToALaterSlot) {
  CallingFromAnEvent run(Direction::kOutput, 77);
  EXPECT_FALSE(run.f.scheduler.HasEvents());
  EXPECT_EQ(run.f.scheduler.CurrentTime().ticks, kCallTime);
}

}  // namespace
