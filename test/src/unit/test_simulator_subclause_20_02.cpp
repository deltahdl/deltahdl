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

std::string RunSource(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

std::string CallAtFive(const std::string& call) {
  return RunSource("module locmod;\n  initial #5 " + call + ";\nendmodule\n");
}

TEST(SimControlSim, DISABLED_TheDiagnosticNamesItsLocation) {
  for (const char* call : {"$finish", "$finish(1)", "$finish(2)", "$stop",
                           "$stop(1)", "$stop(2)"}) {
    std::string out = CallAtFive(call);
    EXPECT_TRUE(out.find("locmod") != std::string::npos ||
                out.find(":2") != std::string::npos)
        << call << ": " << out;
  }
}

TEST(SimControlSim, DISABLED_LevelTwoReportsMemoryAndCpuTime) {
  for (const char* call : {"$finish(2)", "$stop(2)"}) {
    std::string out = CallAtFive(call);
    EXPECT_NE(out.find("memory"), std::string::npos) << call;
    EXPECT_NE(out.find("CPU"), std::string::npos) << call;
    EXPECT_EQ(out.find("unavailable"), std::string::npos) << call;
  }
}

std::string FinishWithVariableLevel(int level) {
  return RunSource("module t;\n  int lvl = " + std::to_string(level) +
                   ";\n  initial #5 $finish(lvl);\nendmodule\n");
}

TEST(SimControlSim, ARunTimeVariableSelectsTheLevel) {
  EXPECT_EQ(FinishWithVariableLevel(0), "");
  std::string level_one = FinishWithVariableLevel(1);
  std::string level_two = FinishWithVariableLevel(2);
  EXPECT_NE(level_one.find("time 5"), std::string::npos);
  EXPECT_GT(level_two.size(), level_one.size());
}

TEST(SimControlSim, StopFromSourceSuspendsTheRunAtItsTime) {
  std::string out = RunSource(
      "module t;\n"
      "  initial #5 $stop;\n"
      "  initial #9 $display(\"later\");\n"
      "endmodule\n");
  EXPECT_NE(out.find("$stop at time 5"), std::string::npos);
  EXPECT_EQ(out.find("later"), std::string::npos);
}

TEST(SimControlSim, DISABLED_StopLeavesTheFinalProceduresUnrun) {
  LowerFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  initial #5 $stop(0);\n"
      "  final x = 7;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  f.scheduler.EndSimulation();
  EXPECT_EQ(x->value.ToUint64(), 0u);
}

TEST(SimControlSim, DISABLED_ExitPrintsTheDiagnosticOfAPlainFinish) {
  std::string out = RunSource(
      "program p;\n"
      "  initial #3 $exit;\n"
      "endprogram\n"
      "module t;\n"
      "  p u();\n"
      "endmodule\n");
  EXPECT_NE(out.find("$finish at time 3"), std::string::npos) << out;
}

TEST(SimControlSim, DISABLED_FinishInAVoidFunctionEndsTheFunction) {
  EXPECT_EQ(RunSource("module t;\n"
                      "  function void stop();\n"
                      "    $display(\"before\");\n"
                      "    $finish(0);\n"
                      "    $display(\"after\");\n"
                      "  endfunction\n"
                      "  initial #1 stop();\n"
                      "endmodule\n"),
            "before\n");
}

TEST(SimControlSim, DISABLED_FinishInAStaticClassFunctionEndsTheFunction) {
  EXPECT_EQ(RunSource("class C;\n"
                      "  static function void stop();\n"
                      "    $display(\"before\");\n"
                      "    $finish(0);\n"
                      "    $display(\"after\");\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  initial #1 C::stop();\n"
                      "endmodule\n"),
            "before\n");
}

TEST(SimControlSim, FinishInAPackageTaskEndsTheTask) {
  EXPECT_EQ(RunSource("package p;\n"
                      "  task run();\n"
                      "    #1 $display(\"before\");\n"
                      "    $finish(0);\n"
                      "    $display(\"after\");\n"
                      "  endtask\n"
                      "endpackage\n"
                      "module t;\n"
                      "  initial p::run();\n"
                      "endmodule\n"),
            "before\n");
}

TEST(SimControlSim, FinishInAProgramEndsTheModulesToo) {
  EXPECT_EQ(RunSource("program pr;\n"
                      "  initial begin\n"
                      "    #2 $display(\"before\");\n"
                      "    $finish(0);\n"
                      "    $display(\"after\");\n"
                      "  end\n"
                      "endprogram\n"
                      "module t;\n"
                      "  pr u();\n"
                      "  initial #5 $display(\"later\");\n"
                      "endmodule\n"),
            "before\n");
}

TEST(SimControlSim, FinishInAnInterfaceEndsTheRun) {
  EXPECT_EQ(RunSource("interface i;\n"
                      "  initial begin\n"
                      "    #2 $display(\"before\");\n"
                      "    $finish(0);\n"
                      "    $display(\"after\");\n"
                      "  end\n"
                      "endinterface\n"
                      "module t;\n"
                      "  i u();\n"
                      "  initial #5 $display(\"later\");\n"
                      "endmodule\n"),
            "before\n");
}

}  // namespace
