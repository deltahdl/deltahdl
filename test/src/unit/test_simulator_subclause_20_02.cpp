#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string EvalCapture(Expr* expr, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  EvalExpr(expr, f.ctx, f.arena);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

TEST(SimControlSim, FinishRequestsStop) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$finish", {});
  EvalCapture(expr, f);
  EXPECT_TRUE(f.ctx.StopRequested());
}

TEST(SimControlSim, StopRequestsStop) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stop", {MkInt(f.arena, 1)});
  EvalCapture(expr, f);
  EXPECT_TRUE(f.ctx.StopRequested());
}

TEST(SimControlSim, FinishDefaultLevelReportsTimeAndLocation) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$finish", {});
  std::string out = EvalCapture(expr, f);
  EXPECT_NE(out.find("$finish"), std::string::npos);
  EXPECT_NE(out.find("time"), std::string::npos);
}

TEST(SimControlSim, FinishLevelZeroPrintsNothing) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$finish", {MkInt(f.arena, 0)});
  std::string out = EvalCapture(expr, f);
  EXPECT_TRUE(out.empty());
}

TEST(SimControlSim, StopLevelOneReportsTimeWithoutStats) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stop", {MkInt(f.arena, 1)});
  std::string out = EvalCapture(expr, f);
  EXPECT_NE(out.find("time"), std::string::npos);
  EXPECT_EQ(out.find("statistics"), std::string::npos);
}

TEST(SimControlSim, StopDefaultLevelReportsTime) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stop", {});
  std::string out = EvalCapture(expr, f);
  EXPECT_NE(out.find("$stop"), std::string::npos);
  EXPECT_NE(out.find("time"), std::string::npos);
}

TEST(SimControlSim, StopLevelZeroPrintsNothing) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stop", {MkInt(f.arena, 0)});
  std::string out = EvalCapture(expr, f);
  EXPECT_TRUE(out.empty());
}

TEST(SimControlSim, FinishLevelTwoAddsStatistics) {
  SysTaskFixture f;
  auto* level_two = MkSysCall(f.arena, "$finish", {MkInt(f.arena, 2)});
  std::string out_two = EvalCapture(level_two, f);
  EXPECT_NE(out_two.find("time"), std::string::npos);
  EXPECT_NE(out_two.find("statistics"), std::string::npos);

  SysTaskFixture g;
  auto* level_one = MkSysCall(g.arena, "$finish", {MkInt(g.arena, 1)});
  std::string out_one = EvalCapture(level_one, g);
  EXPECT_GT(out_two.size(), out_one.size());
}

TEST(SimControlSim, FinishLevelOneReportsTimeWithoutStats) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$finish", {MkInt(f.arena, 1)});
  std::string out = EvalCapture(expr, f);
  EXPECT_NE(out.find("time"), std::string::npos);
  EXPECT_EQ(out.find("statistics"), std::string::npos);
}

TEST(SimControlSim, StopLevelTwoAddsStatistics) {
  SysTaskFixture f;
  auto* level_two = MkSysCall(f.arena, "$stop", {MkInt(f.arena, 2)});
  std::string out_two = EvalCapture(level_two, f);
  EXPECT_NE(out_two.find("time"), std::string::npos);
  EXPECT_NE(out_two.find("statistics"), std::string::npos);

  SysTaskFixture g;
  auto* level_one = MkSysCall(g.arena, "$stop", {MkInt(g.arena, 1)});
  std::string out_one = EvalCapture(level_one, g);
  EXPECT_GT(out_two.size(), out_one.size());
}

TEST(SimControlSim, FinishLevelZeroStillRequestsStop) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$finish", {MkInt(f.arena, 0)});
  EvalCapture(expr, f);
  EXPECT_TRUE(f.ctx.StopRequested());
}

TEST(SimControlSim, StopLevelZeroStillRequestsStop) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stop", {MkInt(f.arena, 0)});
  EvalCapture(expr, f);
  EXPECT_TRUE(f.ctx.StopRequested());
}

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

TEST(SimControlSim, FinishInARandsequenceProductionCodeBlockEndsGeneration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] before_finish, after_finish;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : first second;\n"
      "      first : { before_finish = 8'd37; $finish; };\n"
      "      second : { after_finish = 8'd51; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  EXPECT_TRUE(f.ctx.StopRequested());
  auto* before = f.ctx.FindVariable("before_finish");
  ASSERT_NE(before, nullptr);
  EXPECT_EQ(before->value.ToUint64(), 37u);
  auto* after = f.ctx.FindVariable("after_finish");
  ASSERT_NE(after, nullptr);
  EXPECT_EQ(after->value.ToUint64(), 0u);
}

TEST(SimControlSim, FinishLeavesItsStepsNonblockingAssignmentUnapplied) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  int n = 0;\n"
      "  initial begin\n"
      "    n <= 3;\n"
      "    #1 n <= 5;\n"
      "    $finish(0);\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 3u);
}

TEST(SimControlSim, FinishLeavesItsStepsStrobeUnprinted) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $strobe(\"early\");\n"
      "    #1 $display(\"shown\");\n"
      "    $strobe(\"late\");\n"
      "    $finish(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "early\nshown\n");
}

TEST(SimControlSim, FinishLeavesItsStepsDeferredReportsUnmatured) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int n = 0, observed_fails = 0, final_fails = 0;\n"
      "  function void observed_fail(); observed_fails++; endfunction\n"
      "  function void final_fail(); final_fails++; endfunction\n"
      "  initial begin\n"
      "    assert #0 (n != 0) else observed_fail();\n"
      "    assert final (n != 0) else final_fail();\n"
      "    #1;\n"
      "    assert #0 (n != 0) else observed_fail();\n"
      "    assert final (n != 0) else final_fail();\n"
      "    $finish(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* observed = f.ctx.FindVariable("observed_fails");
  auto* final_fails = f.ctx.FindVariable("final_fails");
  ASSERT_NE(observed, nullptr);
  ASSERT_NE(final_fails, nullptr);
  EXPECT_EQ(observed->value.ToUint64(), 1u);
  EXPECT_EQ(final_fails->value.ToUint64(), 1u);
}

TEST(SimControlSim, FinishInAClassTaskEndsTheTask) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  task run();\n"
                       "    $display(\"before\");\n"
                       "    $finish(0);\n"
                       "    $display(\"after\");\n"
                       "  endtask\n"
                       "endclass\n"
                       "module t;\n"
                       "  C c = new;\n"
                       "  initial c.run();\n"
                       "endmodule\n",
                       f),
            "before\n");
}

TEST(SimControlSim, FinishInAModuleTaskEndsTheTask) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  task run();\n"
                       "    #1 $display(\"before\");\n"
                       "    $finish(0);\n"
                       "    $display(\"after\");\n"
                       "  endtask\n"
                       "  initial run();\n"
                       "endmodule\n",
                       f),
            "before\n");
}

}  // namespace
