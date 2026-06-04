#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Evaluates `$time` at the moment the scheduler has advanced to `at_ticks`,
// returning the value the function reports there. The evaluation runs inside an
// event callback so that the scheduler's current time is the scheduled tick.
uint64_t TimeAtTick(SysTaskFixture& f, uint64_t at_ticks) {
  uint64_t observed = 0;
  auto* event = f.scheduler.GetEventPool().Acquire();
  event->callback = [&]() {
    auto* expr = MkSysCall(f.arena, "$time", {});
    observed = EvalExpr(expr, f.ctx, f.arena).ToUint64();
  };
  f.scheduler.ScheduleEvent(SimTime{at_ticks}, Region::kActive, event);
  f.scheduler.Run();
  return observed;
}

// §20.3.1: $time returns a 64-bit value.
TEST(SysTask, TimeReturnsCurrentTicks) {
  SysTaskFixture f;
  auto* event = f.scheduler.GetEventPool().Acquire();
  event->callback = []() {};
  f.scheduler.ScheduleEvent(SimTime{100}, Region::kActive, event);
  auto* expr = MkSysCall(f.arena, "$time", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.width, 64u);
}

// §20.3.1: the returned value is scaled to the time unit of the invoking
// module. With a 10 ns unit over a 1 ns precision, ten ticks make one unit, so
// simulation time 20 ns (20 ticks) reports as 2.
TEST(SysTask, TimeScaledToModuleUnit) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 10, TimeUnit::kNs, 1});
  EXPECT_EQ(TimeAtTick(f, 20), 2u);
}

// §20.3.1: because $time returns an integer, the scaled value is rounded to the
// nearest integer. 16 ns / (10 ns unit) = 1.6, which rounds up to 2.
TEST(SysTask, TimeRoundsScaledValueUp) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 10, TimeUnit::kNs, 1});
  EXPECT_EQ(TimeAtTick(f, 16), 2u);
}

// §20.3.1 (continued): 32 ns / (10 ns unit) = 3.2, rounding down to 3 — the
// second value from the LRM worked example.
TEST(SysTask, TimeRoundsScaledValueDown) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 10, TimeUnit::kNs, 1});
  EXPECT_EQ(TimeAtTick(f, 32), 3u);
}

// §20.3.1 (rounding tie edge case): a scaled value landing exactly halfway
// between two integers exercises the nearest-integer tie-break. 15 ns over a
// 10 ns unit is 1.5, which the round-to-nearest conversion resolves upward to 2.
TEST(SysTask, TimeRoundsHalfwayValueUp) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 10, TimeUnit::kNs, 1});
  EXPECT_EQ(TimeAtTick(f, 15), 2u);
}

// §20.3.1: a different invoking module with a finer (1 ns) unit over the same
// 1 ns precision applies no scaling, so the same simulation tick reports a
// different value than the 10 ns module above.
TEST(SysTask, TimeUnitOfInvokingModuleControlsScaling) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  EXPECT_EQ(TimeAtTick(f, 16), 16u);
}

// §20.3.1 (edge case for the 64-bit return type): a tick count that does not
// fit in 32 bits must come back in full, unlike the 32-bit $stime. With no
// scaling the reported value equals the tick count, so a value above 2^32
// proves the result is not truncated to the low 32 bits.
TEST(SysTask, TimeIs64BitNotTruncatedTo32) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  constexpr uint64_t big = (uint64_t{1} << 32) + 1u;  // 0x1_0000_0001
  EXPECT_EQ(TimeAtTick(f, big), big);
}

// §20.3.1 (edge case for scaling beyond a single decade): a microsecond unit
// over a nanosecond precision means a thousand ticks make one unit. 3600 ns is
// 3.6 us, which scales and rounds to 4 — exercising a scale factor far larger
// than the factor of ten in the worked example.
TEST(SysTask, TimeScaledAcrossMultipleDecades) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kUs, 1, TimeUnit::kNs, 1});
  EXPECT_EQ(TimeAtTick(f, 3600), 4u);
}

}
