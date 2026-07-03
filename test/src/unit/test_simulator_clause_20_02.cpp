#include <iostream>
#include <sstream>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Evaluates a system-task call while capturing everything it writes to stdout.
std::string EvalCapture(Expr* expr, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  EvalExpr(expr, f.ctx, f.arena);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// §20.2: $finish ends the run; the call requests that the scheduler halt.
TEST(SimControlSim, FinishRequestsStop) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$finish", {});
  EvalCapture(expr, f);
  EXPECT_TRUE(f.ctx.StopRequested());
}

// §20.2: $stop suspends the run; like $finish it halts the scheduler loop.
TEST(SimControlSim, StopRequestsStop) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stop", {MkInt(f.arena, 1)});
  EvalCapture(expr, f);
  EXPECT_TRUE(f.ctx.StopRequested());
}

// §20.2 / Table 20-1: with no argument the diagnostic level defaults to 1, so
// $finish reports the simulation time and the controlling task.
TEST(SimControlSim, FinishDefaultLevelReportsTimeAndLocation) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$finish", {});
  std::string out = EvalCapture(expr, f);
  EXPECT_NE(out.find("$finish"), std::string::npos);
  EXPECT_NE(out.find("time"), std::string::npos);
}

// §20.2 / Table 20-1, level 0: prints nothing.
TEST(SimControlSim, FinishLevelZeroPrintsNothing) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$finish", {MkInt(f.arena, 0)});
  std::string out = EvalCapture(expr, f);
  EXPECT_TRUE(out.empty());
}

// §20.2 / Table 20-1, level 1: prints simulation time and location, but no
// resource-usage statistics.
TEST(SimControlSim, StopLevelOneReportsTimeWithoutStats) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stop", {MkInt(f.arena, 1)});
  std::string out = EvalCapture(expr, f);
  EXPECT_NE(out.find("time"), std::string::npos);
  EXPECT_EQ(out.find("statistics"), std::string::npos);
}

// §20.2 / Table 20-1: the default-level-1 rule is stated for both control
// tasks, so $stop with no argument likewise reports the simulation time.
TEST(SimControlSim, StopDefaultLevelReportsTime) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stop", {});
  std::string out = EvalCapture(expr, f);
  EXPECT_NE(out.find("$stop"), std::string::npos);
  EXPECT_NE(out.find("time"), std::string::npos);
}

// §20.2 / Table 20-1, level 0 applies equally to $stop: nothing is printed.
TEST(SimControlSim, StopLevelZeroPrintsNothing) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stop", {MkInt(f.arena, 0)});
  std::string out = EvalCapture(expr, f);
  EXPECT_TRUE(out.empty());
}

// §20.2 / Table 20-1, level 2: adds the memory and CPU-time statistics line on
// top of the level-1 information.
TEST(SimControlSim, FinishLevelTwoAddsStatistics) {
  SysTaskFixture f;
  auto* level_two = MkSysCall(f.arena, "$finish", {MkInt(f.arena, 2)});
  std::string out_two = EvalCapture(level_two, f);
  EXPECT_NE(out_two.find("time"), std::string::npos);
  EXPECT_NE(out_two.find("statistics"), std::string::npos);

  SysTaskFixture g;
  auto* level_one = MkSysCall(g.arena, "$finish", {MkInt(g.arena, 1)});
  std::string out_one = EvalCapture(level_one, g);
  // Level 2 is strictly more verbose than level 1.
  EXPECT_GT(out_two.size(), out_one.size());
}

// §20.2 / Table 20-1, level 1: the time-and-location rule is stated for both
// control tasks, so $finish at level 1 likewise reports the simulation time
// without the level-2 resource-usage statistics.
TEST(SimControlSim, FinishLevelOneReportsTimeWithoutStats) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$finish", {MkInt(f.arena, 1)});
  std::string out = EvalCapture(expr, f);
  EXPECT_NE(out.find("time"), std::string::npos);
  EXPECT_EQ(out.find("statistics"), std::string::npos);
}

// §20.2 / Table 20-1, level 2 applies equally to $stop: on top of the level-1
// time and location it emits the memory and CPU-time statistics line.
TEST(SimControlSim, StopLevelTwoAddsStatistics) {
  SysTaskFixture f;
  auto* level_two = MkSysCall(f.arena, "$stop", {MkInt(f.arena, 2)});
  std::string out_two = EvalCapture(level_two, f);
  EXPECT_NE(out_two.find("time"), std::string::npos);
  EXPECT_NE(out_two.find("statistics"), std::string::npos);

  SysTaskFixture g;
  auto* level_one = MkSysCall(g.arena, "$stop", {MkInt(g.arena, 1)});
  std::string out_one = EvalCapture(level_one, g);
  // Level 2 carries strictly more detail than level 1.
  EXPECT_GT(out_two.size(), out_one.size());
}

// §20.2: the control action is independent of the diagnostic level. Even at
// level 0, where nothing is printed, $finish still requests that the run halt.
TEST(SimControlSim, FinishLevelZeroStillRequestsStop) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$finish", {MkInt(f.arena, 0)});
  EvalCapture(expr, f);
  EXPECT_TRUE(f.ctx.StopRequested());
}

// §20.2: likewise $stop suspends the run at level 0; the silent diagnostic does
// not suppress the halt request.
TEST(SimControlSim, StopLevelZeroStillRequestsStop) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stop", {MkInt(f.arena, 0)});
  EvalCapture(expr, f);
  EXPECT_TRUE(f.ctx.StopRequested());
}

// §20.2: the diagnostic-level argument is an expression, not only a literal. A
// localparam is a constant expression that resolves during elaboration and
// takes a different path from a literal operand, so this drives the level from
// a localparam end to end -- real source, elaboration, and the run -- rather
// than hand-building the argument node. A value of 2 selects the level-2
// diagnostic, so the memory/CPU statistics line appears and the run halts.
TEST(SimControlSim, FinishLevelFromLocalparamSelectsStatistics) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int LVL = 2;\n"
      "  initial $finish(LVL);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  EXPECT_TRUE(f.ctx.StopRequested());
  EXPECT_NE(captured.str().find("statistics"), std::string::npos);
}

}  // namespace
