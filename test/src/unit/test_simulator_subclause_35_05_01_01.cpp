#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_dpi_bump_import.h"
#include "helpers_dpi_touch_import.h"
#include "parser/ast.h"
#include "simulator/dpi.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// §35.5.1.1: imported functions shall complete their execution instantly and
// consume zero simulation time, just like native SystemVerilog functions.
//
// These tests drive the two production components that together realize that
// rule in the simulator: the Scheduler, which is the authority on simulation
// time, and the DPI runtime, which executes an imported function call. An
// imported function is invoked from inside an event running at a known
// simulation time; the observation is that completing the call neither advances
// the clock nor enqueues any future simulation work — the result is produced
// within the very same time slot. (The companion NOTE that imported *tasks* may
// consume time is non-normative and not exercised here.)

// A trivial imported function that doubles its single int input argument.
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

// The simulation time observed immediately before an imported function call is
// the same as the time observed immediately after it: the call consumes zero
// simulation time.
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

  // The call ran at the event's time and produced its result there...
  EXPECT_EQ(time_before, kCallTime);
  EXPECT_EQ(result, 42);
  // ...and the clock did not move while the imported function executed.
  EXPECT_EQ(time_after, kCallTime);
}

// Completing an imported function call enqueues no future simulation work: the
// scheduler's evaluation-event count is unchanged across the call, the
// next-event horizon stays at the current time, and nothing remains on the
// calendar once the time slot finishes. Scheduling zero future work is what
// "zero simulation time" means for a function — unlike a task, the call cannot
// defer any part of its effect to a later time slot.
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
    // No later time slot is needed to obtain the result, so the next-event
    // horizon remains the current time.
    horizon_after = sched.NextEventTime().ticks;
  };
  sched.ScheduleEvent({kCallTime}, Region::kActive, ev);
  sched.Run();

  // The imported call scheduled nothing of its own.
  EXPECT_EQ(scheduled_after, scheduled_before);
  EXPECT_EQ(horizon_after, kCallTime);
  // Nothing was deferred to a future time slot.
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(sched.CurrentTime().ticks, kCallTime);
}

// Edge case: several imported function calls made back-to-back within a single
// time slot still consume zero simulation time in aggregate. Instant completion
// is per call, so no number of calls advances the clock or defers work.
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
  // The clock did not move across five successive imported calls...
  EXPECT_EQ(time_after, kCallTime);
  // ...and none of them deferred any work to a later time slot.
  EXPECT_EQ(scheduled_after, scheduled_before);
  EXPECT_EQ(last, 8);  // 4 * 2 from the final iteration
}

// Edge case: an imported function that produces a side effect through an output
// formal (the heavier output-writeback path) is still instantaneous. Writing
// its formals does not let an imported *function* consume simulation time the
// way a task could; completion and the writeback both happen within the slot.
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

  // The output was produced...
  EXPECT_EQ(written, 77);
  // ...instantly, with zero simulation time consumed.
  EXPECT_EQ(time_before, kCallTime);
  EXPECT_EQ(time_after, kCallTime);
}

// Edge case: the heaviest import entry point — the one that copies back an
// inout actual and then detects the resulting value change — still completes
// within the same time slot. Detecting and reporting the change happens after
// the foreign function returns but as part of the very same synchronous call:
// the change is delivered into the caller's vector, never scheduled onto the
// simulator's calendar, so no number of value changes lets an imported
// function consume simulation time or defer work to a later slot.
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

  // The change-detecting path actually ran and observed the inout change...
  EXPECT_EQ(change_count, 1u);
  EXPECT_EQ(new_value, 42);
  // ...all within the call's own time slot: the clock never moved and nothing
  // was deferred onto the calendar.
  EXPECT_EQ(time_before, kCallTime);
  EXPECT_EQ(time_after, kCallTime);
  EXPECT_EQ(scheduled_after, scheduled_before);
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(sched.CurrentTime().ticks, kCallTime);
}

// ---------------------------------------------------------------------------
// The same rule, asked of a call a design makes.
//
// The cases above call the foreign function through DpiRuntime. A call written
// in SystemVerilog does not reach it: EvalDpiCall in
// src/simulator/eval_function.cpp is what evaluates one, and §35.5.1.2 has it
// assign to the actual written against an output or an inout formal once the
// foreign function returns. An assignment is the one thing in that call that
// can put work on the calendar, so the rule is asked here of the call site that
// makes them.
// ---------------------------------------------------------------------------

// One call to `touch(a)`, made from inside an event running at kCallTime.
//
// What the case reads afterwards is the state at the moment the foreign
// function returned: the clock the call site saw, and the value the design's
// variable held there. Reading the variable inside the event is the whole
// point, because a value that only arrives later is exactly what a call
// consuming simulation time would produce.
struct CallingFromAnEvent {
  DpiContext dpi;
  SimFixture f;
  uint64_t seen = 0;
  uint64_t time_after = 0;
  uint64_t actual_in_slot = 0;

  CallingFromAnEvent(Direction direction, uint64_t wrote) {
    RegisterTouchImport(dpi, direction, wrote, &seen);
    f.ctx.SetDpiContext(&dpi);
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

// §35.5.1.1: an imported function consumes zero simulation time, so the clock
// the call site reads when the call returns is the one it was called at.
TEST(DpiInstantCompletion, ADesignsImportedCallReturnsAtTheTimeItWasMadeAt) {
  CallingFromAnEvent run(Direction::kInput, 111);
  EXPECT_EQ(run.time_after, kCallTime);
}

// §35.5.1.1: and it completes instantly, so what the function wrote to an
// output argument is in the design's variable before the time slot the call was
// made in has finished. A copy-back deferred to a later slot would leave the
// variable holding what it held.
TEST(DpiInstantCompletion, ADesignsOutputArgumentIsWrittenInTheCallsOwnSlot) {
  CallingFromAnEvent run(Direction::kOutput, 77);
  EXPECT_EQ(run.actual_in_slot, 77U);
}

// The other thing a call that finished instantly leaves behind: nothing on the
// calendar. Writing the output argument assigns to a variable, which is the one
// part of an imported call that can schedule anything, and the run ends with
// the slot the call was made in rather than at a later time.
TEST(DpiInstantCompletion, ADesignsImportedCallDefersNothingToALaterSlot) {
  CallingFromAnEvent run(Direction::kOutput, 77);
  EXPECT_FALSE(run.f.scheduler.HasEvents());
  EXPECT_EQ(run.f.scheduler.CurrentTime().ticks, kCallTime);
}

}  // namespace
