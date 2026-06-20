#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// The parser models a bare $root/$unit argument as an argument-less system
// call, so reproduce that shape when driving the evaluator directly.
Expr* MkScopeArg(Arena& arena, std::string_view name) {
  return MkSysCall(arena, name, {});
}

// §20.4.2: with no argument, $printtimescale describes the design element that
// is the current scope, naming it and reporting its unit and precision.
TEST(PrinttimescaleSysTask, NoArgumentDescribesCurrentScope) {
  SysTaskFixture f;
  f.ctx.SetCurrentScopeName("a_dat");
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kMs, 1, TimeUnit::kUs, 1});
  auto* call = MkSysCall(f.arena, "$printtimescale", {});
  EXPECT_EQ(BuildPrinttimescaleReport(call, f.ctx),
            "Time scale of (a_dat) is 1ms / 1us");
}

// §20.4.2: a named argument selects that design element; its name appears in
// the report and its own time unit and precision are shown.
TEST(PrinttimescaleSysTask, NamedElementArgumentDescribesThatElement) {
  SysTaskFixture f;
  f.ctx.SetScopeTimeScale("b_dat.c1",
                          TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  auto* call =
      MkSysCall(f.arena, "$printtimescale", {MkId(f.arena, "b_dat.c1")});
  EXPECT_EQ(BuildPrinttimescaleReport(call, f.ctx),
            "Time scale of (b_dat.c1) is 1ns / 1ns");
}

// §20.4.2: the $unit argument describes the compilation unit, and the literal
// "$unit" stands in for the design-element name.
TEST(PrinttimescaleSysTask, UnitArgumentDescribesCompilationUnit) {
  SysTaskFixture f;
  f.ctx.SetCompUnitTimeScale(TimeScale{TimeUnit::kPs, 100, TimeUnit::kFs, 10});
  auto* call =
      MkSysCall(f.arena, "$printtimescale", {MkScopeArg(f.arena, "$unit")});
  EXPECT_EQ(BuildPrinttimescaleReport(call, f.ctx),
            "Time scale of ($unit) is 100ps / 10fs");
}

// §20.4.2: the $root argument describes the simulation time unit, and the
// literal "$root" stands in for the design-element name. The simulation time
// unit and global precision are synonymous, so both fields are identical.
TEST(PrinttimescaleSysTask, RootArgumentDescribesSimulationTimeUnit) {
  SysTaskFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kFs);
  auto* call =
      MkSysCall(f.arena, "$printtimescale", {MkScopeArg(f.arena, "$root")});
  EXPECT_EQ(BuildPrinttimescaleReport(call, f.ctx),
            "Time scale of ($root) is 1fs / 1fs");
}

// §20.4.2 (shall): the report follows the fixed format
// "Time scale of (<name>) is <unit> / <precision>". An off-decade magnitude
// (10 ns, here as the precision) exercises the Table 20-2 rendering.
TEST(PrinttimescaleSysTask, ReportFollowsRequiredFormat) {
  SysTaskFixture f;
  f.ctx.SetScopeTimeScale("dut",
                          TimeScale{TimeUnit::kUs, 100, TimeUnit::kNs, 10});
  auto* call = MkSysCall(f.arena, "$printtimescale", {MkId(f.arena, "dut")});
  EXPECT_EQ(BuildPrinttimescaleReport(call, f.ctx),
            "Time scale of (dut) is 100us / 10ns");
}

// §20.4.2 (shall) edge case: the report renders whole-second units at the top
// of Table 20-2 (orders 2 and 1), exercising the positive-order branch of the
// magnitude-and-unit formatting that the sub-second cases never reach.
TEST(PrinttimescaleSysTask, RendersWholeSecondUnits) {
  SysTaskFixture f;
  f.ctx.SetScopeTimeScale("slow",
                          TimeScale{TimeUnit::kS, 100, TimeUnit::kS, 10});
  auto* call = MkSysCall(f.arena, "$printtimescale", {MkId(f.arena, "slow")});
  EXPECT_EQ(BuildPrinttimescaleReport(call, f.ctx),
            "Time scale of (slow) is 100s / 10s");
}

// Edge case: with no timescale configured the current scope defaults to 1 ns
// for both unit and precision.
TEST(PrinttimescaleSysTask, DefaultCurrentScopeIsNanosecond) {
  SysTaskFixture f;
  f.ctx.SetCurrentScopeName("top");
  auto* call = MkSysCall(f.arena, "$printtimescale", {});
  EXPECT_EQ(BuildPrinttimescaleReport(call, f.ctx),
            "Time scale of (top) is 1ns / 1ns");
}

// §20.4.2: $printtimescale displays the timescale report. Drive the full
// evaluator dispatch and capture stdout so the emitted line is observed
// end to end, not just the report string the task assembles.
TEST(PrinttimescaleSysTask, TaskDisplaysReportLineToStdout) {
  SysTaskFixture f;
  f.ctx.SetCurrentScopeName("a_dat");
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kMs, 1, TimeUnit::kUs, 1});
  auto* call = MkSysCall(f.arena, "$printtimescale", {});
  testing::internal::CaptureStdout();
  EvalExpr(call, f.ctx, f.arena);
  std::string out = testing::internal::GetCapturedStdout();
  EXPECT_EQ(out, "Time scale of (a_dat) is 1ms / 1us\n");
}

}  // namespace
