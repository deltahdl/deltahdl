#include <cstring>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Evaluates `$realtime` once the scheduler has advanced to `at_ticks` and
// returns the real value it reports there. The evaluation runs inside an event
// callback so that the scheduler's current time is the scheduled tick. The
// result carries a real number in its 64-bit payload, so the bit pattern is
// reinterpreted as a double.
double RealtimeAtTick(SysTaskFixture& f, uint64_t at_ticks) {
  double observed = 0.0;
  auto* event = f.scheduler.GetEventPool().Acquire();
  event->callback = [&]() {
    auto* expr = MkSysCall(f.arena, "$realtime", {});
    uint64_t bits = EvalExpr(expr, f.ctx, f.arena).ToUint64();
    std::memcpy(&observed, &bits, sizeof(double));
  };
  f.scheduler.ScheduleEvent(SimTime{at_ticks}, Region::kActive, event);
  f.scheduler.Run();
  return observed;
}

// §20.3.3: $realtime returns a 64-bit value.
TEST(SysTask, RealtimeReturns64Bit) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$realtime", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 64u);
}

// §20.3.3: $realtime returns a real number, not an integer. The simulator marks
// a value as real with the is_real flag, which downstream consumers (e.g. the
// display tasks) rely on to format the time as a real quantity.
TEST(SysTask, RealtimeReturnsRealNumber) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$realtime", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
}

// §20.3.3: like $time, the reported value is scaled to the invoking module's
// time unit. With a 10 ns unit over a 1 ns precision, ten ticks make one unit,
// so simulation time 20 ns (20 ticks) reports as 2.0 rather than 20.
TEST(SysTask, RealtimeScaledToModuleUnit) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 10, TimeUnit::kNs, 1});
  EXPECT_DOUBLE_EQ(RealtimeAtTick(f, 20), 2.0);
}

// §20.3.3 (LRM example, `timescale 10 ns / 1 ns): event times 16 ns and 32 ns
// are reported by $realtime as the real numbers 1.6 and 3.2 — multiples of the
// 10 ns unit, with the fraction preserved rather than rounded. Keeping the
// fraction (1.6 rather than $time's 2) is what distinguishes $realtime.
TEST(SysTask, RealtimeMatchesLrmExample) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 10, TimeUnit::kNs, 1});
  EXPECT_DOUBLE_EQ(RealtimeAtTick(f, 16), 1.6);
  EXPECT_DOUBLE_EQ(RealtimeAtTick(f, 32), 3.2);
}

// §20.3.3 (R2 scaling, degenerate case): when the module's time unit equals its
// precision, one tick is exactly one unit, so the scale factor is 1 and the
// reported time equals the raw tick count — but still as a real number. This
// exercises the no-scaling branch of the scaling computation.
TEST(SysTask, RealtimeUnscaledWhenUnitEqualsPrecision) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  EXPECT_DOUBLE_EQ(RealtimeAtTick(f, 7), 7.0);
}

// §20.3.3 (R1 + R2, multi-decade scaling): a unit several decades coarser than
// the precision divides the tick count by a correspondingly larger factor,
// and the real result keeps any remaining fraction. With a 100 ns unit over a
// 1 ns precision, 250 ticks scale to 2.5.
TEST(SysTask, RealtimeScalesAcrossMultipleDecades) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 100, TimeUnit::kNs, 1});
  EXPECT_DOUBLE_EQ(RealtimeAtTick(f, 250), 2.5);
}

}
