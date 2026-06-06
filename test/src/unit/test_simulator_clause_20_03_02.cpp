#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Evaluates `$stime` once the scheduler has advanced to `at_ticks`, returning
// the value the function reports there. The evaluation runs inside an event
// callback so that the scheduler's current time is the scheduled tick.
uint64_t StimeAtTick(SysTaskFixture& f, uint64_t at_ticks) {
  uint64_t observed = 0;
  auto* event = f.scheduler.GetEventPool().Acquire();
  event->callback = [&]() {
    auto* expr = MkSysCall(f.arena, "$stime", {});
    observed = EvalExpr(expr, f.ctx, f.arena).ToUint64();
  };
  f.scheduler.ScheduleEvent(SimTime{at_ticks}, Region::kActive, event);
  f.scheduler.Run();
  return observed;
}

// §20.3.2: $stime returns a 32-bit value.
TEST(SysTask, StimeReturns32Bit) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stime", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

// §20.3.2: the reported time is scaled to the invoking module's time unit, just
// as $time is. With a 10 ns unit over a 1 ns precision, ten ticks make one
// unit, so simulation time 20 ns (20 ticks) reports as 2 rather than 20.
TEST(SysTask, StimeScaledToModuleUnit) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 10, TimeUnit::kNs, 1});
  EXPECT_EQ(StimeAtTick(f, 20), 2u);
}

// §20.3.2: when the scaled simulation time does not fit in 32 bits, only the
// low-order 32 bits are returned. With a 1 ns unit over a 1 ns precision no
// scaling occurs, so a tick count just past 2^32 comes back as its low 32 bits.
TEST(SysTask, StimeTruncatesToLow32Bits) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  constexpr uint64_t big = (uint64_t{1} << 32) + 5u;  // 0x1_0000_0005
  EXPECT_EQ(StimeAtTick(f, big), 5u);
}

// §20.3.2 (ordering of scaling and truncation): when the raw tick count exceeds
// 32 bits but the value scaled to the module unit fits in 32 bits, the full
// scaled value is reported. This proves scaling happens before the 32-bit
// narrowing — truncating the raw ticks first would yield a different result.
// 5e9 ticks (above 2^32) over a 10 ns unit / 1 ns precision is 500,000,000,
// which fits in 32 bits.
TEST(SysTask, StimeScalesLargeTimeBeforeTruncating) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 10, TimeUnit::kNs, 1});
  EXPECT_EQ(StimeAtTick(f, 5'000'000'000ull), 500'000'000u);
}

// §20.3.2 (truncation boundary edge): a scaled time of exactly 2^32 has all of
// its low-order 32 bits clear, so the reported value is 0 rather than anything
// derived from the discarded high bits. This pins the result to precisely the
// low 32 bits at the wrap boundary, complementing the just-past-boundary case.
TEST(SysTask, StimeWrapsToZeroAtExact32BitBoundary) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  constexpr uint64_t boundary = uint64_t{1} << 32;  // 0x1_0000_0000
  EXPECT_EQ(StimeAtTick(f, boundary), 0u);
}

// §20.3.2 (unsigned 32-bit return, boundary): a value whose top 32-bit bit is
// set is reported in full as an unsigned quantity, not narrowed or sign-folded.
TEST(SysTask, StimeReportsFullUnsigned32BitRange) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  constexpr uint64_t high = uint64_t{0x80000001};
  EXPECT_EQ(StimeAtTick(f, high), 0x80000001u);
}

}
