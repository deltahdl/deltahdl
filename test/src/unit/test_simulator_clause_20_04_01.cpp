#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// The parser models a bare $root/$unit argument as an argument-less system
// call, so reproduce that shape when driving the evaluator directly.
Expr* MkScopeArg(Arena& arena, std::string_view name) {
  return MkSysCall(arena, name, {});
}

int32_t EvalOrder(SimFixture& f, Expr* call) {
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_TRUE(result.is_signed);
  return static_cast<int32_t>(result.ToUint64());
}

// No argument: $timeunit reports the time unit of the current scope, encoded
// per Table 20-2 (10 ns -> -8).
TEST(TimescaleSystemFunctions, TimeunitNoArgReturnsCurrentScopeUnit) {
  SysTaskFixture f;
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 10, TimeUnit::kPs, 1});
  EXPECT_EQ(EvalOrder(f, MkSysCall(f.arena, "$timeunit", {})), -8);
}

// No argument: $timeprecision reports the precision of the current scope
// (1 ps -> -12), distinct from the time unit.
TEST(TimescaleSystemFunctions, TimeprecisionNoArgReturnsCurrentScopePrecision) {
  SysTaskFixture f;
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 10, TimeUnit::kPs, 1});
  EXPECT_EQ(EvalOrder(f, MkSysCall(f.arena, "$timeprecision", {})), -12);
}

// A named design-element argument reports that element's timescale
// (100 us -> -4).
TEST(TimescaleSystemFunctions, TimeunitNamedElementArgument) {
  SysTaskFixture f;
  f.ctx.SetScopeTimeScale("dut",
                          TimeScale{TimeUnit::kUs, 100, TimeUnit::kNs, 1});
  auto* call = MkSysCall(f.arena, "$timeunit", {MkId(f.arena, "dut")});
  EXPECT_EQ(EvalOrder(f, call), -4);
}

// The $unit argument reports the compilation unit's timescale (1 s -> 0 unit,
// 1 ms -> -3 precision).
TEST(TimescaleSystemFunctions, UnitArgumentReportsCompilationUnit) {
  SysTaskFixture f;
  f.ctx.SetCompUnitTimeScale(TimeScale{TimeUnit::kS, 1, TimeUnit::kMs, 1});
  auto* unit = MkSysCall(f.arena, "$timeunit", {MkScopeArg(f.arena, "$unit")});
  auto* prec =
      MkSysCall(f.arena, "$timeprecision", {MkScopeArg(f.arena, "$unit")});
  EXPECT_EQ(EvalOrder(f, unit), 0);
  EXPECT_EQ(EvalOrder(f, prec), -3);
}

// The $root argument yields the simulation time unit for both functions.
TEST(TimescaleSystemFunctions, RootArgumentReturnsSimulationTimeUnit) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kFs);
  auto* unit = MkSysCall(f.arena, "$timeunit", {MkScopeArg(f.arena, "$root")});
  auto* prec =
      MkSysCall(f.arena, "$timeprecision", {MkScopeArg(f.arena, "$root")});
  EXPECT_EQ(EvalOrder(f, unit), -15);
  EXPECT_EQ(EvalOrder(f, prec), -15);
}

// Edge case: with no timescale configured the current scope defaults to 1 ns,
// so both functions report -9.
TEST(TimescaleSystemFunctions, DefaultCurrentScopeIsNanosecond) {
  SysTaskFixture f;
  EXPECT_EQ(EvalOrder(f, MkSysCall(f.arena, "$timeunit", {})), -9);
  EXPECT_EQ(EvalOrder(f, MkSysCall(f.arena, "$timeprecision", {})), -9);
}

// Edge case: a magnitude of 10 or 100 raises the Table 20-2 order by one or
// two, producing the off-decade values (10 s -> 1, 100 ns -> -7, 100 ms -> -1).
TEST(TimescaleSystemFunctions, MagnitudeMultiplierShiftsTableOrder) {
  SysTaskFixture f;
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kS, 10, TimeUnit::kNs, 100});
  EXPECT_EQ(EvalOrder(f, MkSysCall(f.arena, "$timeunit", {})), 1);
  EXPECT_EQ(EvalOrder(f, MkSysCall(f.arena, "$timeprecision", {})), -7);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kMs, 100, TimeUnit::kMs, 1});
  EXPECT_EQ(EvalOrder(f, MkSysCall(f.arena, "$timeunit", {})), -1);
}

// The return value is an integer within the Table 20-2 range of 2 to -15.
TEST(TimescaleSystemFunctions, ReturnValueWithinTableRange) {
  SysTaskFixture f;
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kS, 100, TimeUnit::kFs, 1});
  int32_t unit = EvalOrder(f, MkSysCall(f.arena, "$timeunit", {}));
  int32_t prec = EvalOrder(f, MkSysCall(f.arena, "$timeprecision", {}));
  EXPECT_EQ(unit, 2);    // 100 s, the maximum
  EXPECT_EQ(prec, -15);  // 1 fs, the minimum
  EXPECT_LE(unit, 2);
  EXPECT_GE(prec, -15);
}

}  // namespace
