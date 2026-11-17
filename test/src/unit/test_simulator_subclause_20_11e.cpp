#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <string>
#include <vector>

#include "helpers_assert_control_runs.h"

using namespace delta;

namespace {

TEST(AssertScopeControlSim, ALockedAssertionIgnoresAnActionControl) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    $assertcontrol(1);\n"
      "    $assertfailoff;\n"
      "    assert (0) else $display(\"task\");\n"
      "    $assertcontrol(9);\n"
      "    assert (0) else $display(\"control\");\n"
      "    $assertcontrol(2);\n"
      "    $assertfailoff;\n"
      "    assert (0) else $display(\"unlocked\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "task\ncontrol\n");
}

TEST(AssertScopeControlSim, ALockedAssertionIgnoresKillAndOn) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    $assertcontrol(1);\n"
      "    $assertkill;\n"
      "    assert (0) else $display(\"after kill\");\n"
      "    $assertcontrol(2);\n"
      "    $assertoff;\n"
      "    $assertcontrol(1);\n"
      "    $asserton;\n"
      "    assert (0) else $display(\"after on\");\n"
      "    $assertcontrol(2);\n"
      "    $asserton;\n"
      "    assert (0) else $display(\"unlocked\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "after kill\nunlocked\n");
}

TEST(AssertScopeControlSim, AKillLeavesTheAttemptOfALockedAssertionInFlight) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (6) #5 clk = ~clk;\n"
      "  assert property (@(posedge clk) 1 |-> ##2 0) else $display(\"f %0t\", "
      "$time);\n"
      "  initial begin\n"
      "    $assertcontrol(1);\n"
      "    #10 $assertkill;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "f 25\n");
}

TEST(AssertScopeControlSim,
     LockedImmediateAndDeferredAssertionsIgnoreOffUntilUnlock) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    $assertcontrol(1, 14);\n"
      "    $assertoff;\n"
      "    assert (0) else $display(\"simple\");\n"
      "    assert #0 (0) else $display(\"observed\");\n"
      "    assert final (0) else $display(\"final\");\n"
      "    #1 $assertcontrol(2, 14);\n"
      "    $assertoff;\n"
      "    assert (0) else $display(\"simple unlocked\");\n"
      "    assert #0 (0) else $display(\"observed unlocked\");\n"
      "    assert final (0) else $display(\"final unlocked\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "simple\nobserved\nfinal\n");
}

TEST(AssertScopeControlSim, ALockedExpectIgnoresOff) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (2) #5 clk = ~clk;\n"
      "  initial begin\n"
      "    $assertcontrol(1, 16);\n"
      "    $assertcontrol(4, 16);\n"
      "    expect (@(posedge clk) 0) else $display(\"f %0t\", $time);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "f 5\n");
}

TEST(AssertScopeControlSim, LockedViolationReportsIgnoreOffUntilUnlock) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(1, 32);\n"
      "    $assertcontrol(4, 32);\n"
      "    unique if (x == 1) y = 1;\n"
      "    $assertcontrol(2, 32);\n"
      "    $assertcontrol(4, 32);\n"
      "    unique if (x == 1) y = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "6");
}

TEST(AssertScopeControlSim, ADeferredReportQueuedBeforeOffStillMatures) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    assert #0 (0) else $display(\"observed\");\n"
      "    assert final (0) else $display(\"final\");\n"
      "    $assertoff;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "observed\nfinal\n");
}

TEST(AssertScopeControlSim,
     DISABLED_APendingProceduralInstanceQueuedBeforeOffStillMatures) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (6) #5 clk = ~clk;\n"
      "  bit b = 0;\n"
      "  always @(posedge clk) begin\n"
      "    p1: assert property (@(posedge clk) b) else $display(\"f %0t\", "
      "$time);\n"
      "    if ($time == 15) $assertoff;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "f 5\nf 15\n");
}

TEST(AssertScopeControlSim, AViolationReportQueuedBeforeOffStillMatures) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    unique if (x == 1) y = 1;\n"
      "    $assertcontrol(4, 32);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "4");
}

TEST(AssertScopeControlSim, AnExpectRunsUnderAnOffSelectingIt) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (2) #5 clk = ~clk;\n"
      "  initial begin\n"
      "    $assertcontrol(4);\n"
      "    expect (@(posedge clk) 0) else $display(\"f %0t\", $time);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "f 5\n");
}

TEST(AssertScopeControlSim, AKillFlushesAQueuedDeferredReport) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    assert #0 (0) else $display(\"observed\");\n"
      "    assert final (0) else $display(\"final\");\n"
      "    $assertkill;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "");
}

TEST(AssertScopeControlSim, AKillFlushesAPendingProceduralInstance) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (6) #5 clk = ~clk;\n"
      "  bit b = 0;\n"
      "  always @(posedge clk) begin\n"
      "    p1: assert property (@(posedge clk) b) else $display(\"f %0t\", "
      "$time);\n"
      "    if ($time == 15) $assertkill;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "f 5\n");
}

TEST(AssertScopeControlSim, NoViolationReportIsMadeBetweenAKillAndTheNextOn) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(5);\n"
      "    unique if (x == 1) y = 1;\n"
      "    $assertcontrol(3);\n"
      "    unique if (x == 1) y = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "7");
}

TEST(AssertScopeControlSim, AKillOfConcurrentAssertsLeavesCoversAndAssumes) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (4) #5 clk = ~clk;\n"
      "  a1: assert property (@(posedge clk) 0) else $display(\"assert %0t\", "
      "$time);\n"
      "  m1: assume property (@(posedge clk) 0) else $display(\"assume %0t\", "
      "$time);\n"
      "  c1: cover property (@(posedge clk) 1) $display(\"cover %0t\", "
      "$time);\n"
      "  initial #10 $assertcontrol(5, 1, 1);\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "assert 5\nassume 5\ncover 5\nassume 15\ncover 15\n");
}

TEST(AssertScopeControlSim, AKillLeavesAnExpect) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (2) #5 clk = ~clk;\n"
      "  initial begin\n"
      "    $assertcontrol(5);\n"
      "    expect (@(posedge clk) 0) else $display(\"f %0t\", $time);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "f 5\n");
}

TEST(AssertScopeControlSim, LevelsZeroReachesEveryDepthBelowTheScope) {
  ControlRun r = RunControlled(
      "module l3;\n"
      "  initial #3 assert (0) else $display(\"l3\");\n"
      "endmodule\n"
      "module l2;\n"
      "  l3 x();\n"
      "  initial #2 assert (0) else $display(\"l2\");\n"
      "endmodule\n"
      "module l1;\n"
      "  l2 y();\n"
      "  initial #1 assert (0) else $display(\"l1\");\n"
      "endmodule\n"
      "module t;\n"
      "  l1 u();\n"
      "  initial $assertoff(0, u);\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "");
}

TEST(AssertScopeControlSim, LevelsOneReachesTheScopeAlone) {
  ControlRun r = RunControlled(
      "module l3;\n"
      "  initial #3 assert (0) else $display(\"l3\");\n"
      "endmodule\n"
      "module l2;\n"
      "  l3 x();\n"
      "  initial #2 assert (0) else $display(\"l2\");\n"
      "endmodule\n"
      "module l1;\n"
      "  l2 y();\n"
      "  initial #1 assert (0) else $display(\"l1\");\n"
      "endmodule\n"
      "module t;\n"
      "  l1 u();\n"
      "  initial $assertoff(1, u);\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "l2\nl3\n");
}

TEST(AssertScopeControlSim, LevelsTwoReachesTheScopeAndOneLevelBelow) {
  ControlRun r = RunControlled(
      "module l3;\n"
      "  initial #3 assert (0) else $display(\"l3\");\n"
      "endmodule\n"
      "module l2;\n"
      "  l3 x();\n"
      "  initial #2 assert (0) else $display(\"l2\");\n"
      "endmodule\n"
      "module l1;\n"
      "  l2 y();\n"
      "  initial #1 assert (0) else $display(\"l1\");\n"
      "endmodule\n"
      "module t;\n"
      "  l1 u();\n"
      "  initial $assertoff(2, u);\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "l3\n");
}

TEST(AssertScopeControlSim, AnEmptyLevelsArgumentDefaultsToZero) {
  ControlRun r = RunControlled(
      "module l3;\n"
      "  initial #3 assert (0) else $display(\"l3\");\n"
      "endmodule\n"
      "module l2;\n"
      "  l3 x();\n"
      "  initial #2 assert (0) else $display(\"l2\");\n"
      "endmodule\n"
      "module l1;\n"
      "  l2 y();\n"
      "  initial #1 assert (0) else $display(\"l1\");\n"
      "endmodule\n"
      "module t;\n"
      "  l1 u();\n"
      "  initial $assertcontrol(4, , , , u);\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "");
}

TEST(AssertScopeControlSim, LevelsFromAParameter) {
  ControlRun r = RunControlled(
      "module l3;\n"
      "  initial #3 assert (0) else $display(\"l3\");\n"
      "endmodule\n"
      "module l2;\n"
      "  l3 x();\n"
      "  initial #2 assert (0) else $display(\"l2\");\n"
      "endmodule\n"
      "module l1;\n"
      "  l2 y();\n"
      "  initial #1 assert (0) else $display(\"l1\");\n"
      "endmodule\n"
      "module t;\n"
      "  l1 u();\n"
      "  localparam int N = 1;\n"
      "  initial $assertoff(N, u);\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "l2\nl3\n");
}

TEST(AssertScopeControlSim, LevelsFromAVariable) {
  ControlRun r = RunControlled(
      "module l3;\n"
      "  initial #3 assert (0) else $display(\"l3\");\n"
      "endmodule\n"
      "module l2;\n"
      "  l3 x();\n"
      "  initial #2 assert (0) else $display(\"l2\");\n"
      "endmodule\n"
      "module l1;\n"
      "  l2 y();\n"
      "  initial #1 assert (0) else $display(\"l1\");\n"
      "endmodule\n"
      "module t;\n"
      "  l1 u();\n"
      "  int n;\n"
      "  initial begin\n"
      "    n = 2;\n"
      "    $assertoff(n, u);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "l3\n");
}

std::string SortedLines(const std::string& out) {
  std::vector<std::string> lines;
  size_t start = 0;
  while (start < out.size()) {
    size_t end = out.find('\n', start);
    lines.push_back(out.substr(start, end - start));
    start = end + 1;
  }
  std::sort(lines.begin(), lines.end());
  std::string joined;
  for (const auto& line : lines) joined += line + " ";
  return joined;
}

std::string ControlledLines(const std::string& src) {
  return SortedLines(ControlledOutput(src));
}

TEST(AssertScopeControlSim, AnInstanceInTheListStopsTheAssertionsInsideIt) {
  EXPECT_EQ(ControlledLines("module sub;\n"
                            "  a1: assert final (0) else $display(\"u.a1\");\n"
                            "  a2: assert final (0) else $display(\"u.a2\");\n"
                            "endmodule\n"
                            "module t;\n"
                            "  sub u();\n"
                            "  ax: assert final (0) else $display(\"ax\");\n"
                            "  ay: assert final (0) else $display(\"ay\");\n"
                            "  initial $assertoff(0, t.u);\n"
                            "endmodule\n"),
            "ax ay ");
}

TEST(AssertScopeControlSim,
     ANamedAssertionInAnActionTaskListIsControlledAlone) {
  EXPECT_EQ(ControlledLines("module sub;\n"
                            "  a1: assert final (0) else $display(\"u.a1\");\n"
                            "  a2: assert final (0) else $display(\"u.a2\");\n"
                            "endmodule\n"
                            "module t;\n"
                            "  sub u();\n"
                            "  ax: assert final (0) else $display(\"ax\");\n"
                            "  ay: assert final (0) else $display(\"ay\");\n"
                            "  initial $assertfailoff(0, t.u.a1);\n"
                            "endmodule\n"),
            "ax ay u.a2 ");
}

TEST(AssertScopeControlSim, ScopesAndAssertionsMixInOneList) {
  EXPECT_EQ(ControlledLines("module sub;\n"
                            "  a1: assert final (0) else $display(\"u.a1\");\n"
                            "  a2: assert final (0) else $display(\"u.a2\");\n"
                            "endmodule\n"
                            "module t;\n"
                            "  sub u();\n"
                            "  ax: assert final (0) else $display(\"ax\");\n"
                            "  ay: assert final (0) else $display(\"ay\");\n"
                            "  initial $assertoff(0, t.u, ay);\n"
                            "endmodule\n"),
            "ax ");
}

TEST(AssertScopeControlSim,
     AHierarchicalNameSelectsAnAssertionInAnotherInstance) {
  EXPECT_EQ(ControlledLines("module sub;\n"
                            "  a1: assert final (0) else $display(\"u.a1\");\n"
                            "  a2: assert final (0) else $display(\"u.a2\");\n"
                            "endmodule\n"
                            "module t;\n"
                            "  sub u();\n"
                            "  ax: assert final (0) else $display(\"ax\");\n"
                            "  ay: assert final (0) else $display(\"ay\");\n"
                            "  initial $assertoff(0, t.u.a1);\n"
                            "endmodule\n"),
            "ax ay u.a2 ");
}

TEST(AssertScopeControlSim, AGenerateBlockInTheListControlsItsAssertionsAlone) {
  EXPECT_EQ(ControlledLines("module sub;\n"
                            "  a1: assert final (0) else $display(\"u.a1\");\n"
                            "  a2: assert final (0) else $display(\"u.a2\");\n"
                            "endmodule\n"
                            "module t;\n"
                            "  sub u();\n"
                            "  if (1) begin : g\n"
                            "    ag: assert final (0) else $display(\"g\");\n"
                            "  end\n"
                            "  ax: assert final (0) else $display(\"ax\");\n"
                            "  ay: assert final (0) else $display(\"ay\");\n"
                            "  initial $assertoff(0, t.g);\n"
                            "endmodule\n"),
            "ax ay u.a1 u.a2 ");
}

TEST(AssertScopeControlSim,
     AInterfaceInstanceInTheListControlsItsAssertionsAlone) {
  EXPECT_EQ(ControlledLines("interface I;\n"
                            "  ai: assert final (0) else $display(\"i\");\n"
                            "endinterface\n"
                            "module sub;\n"
                            "  a1: assert final (0) else $display(\"u.a1\");\n"
                            "  a2: assert final (0) else $display(\"u.a2\");\n"
                            "endmodule\n"
                            "module t;\n"
                            "  sub u();\n"
                            "  I i();\n"
                            "  ax: assert final (0) else $display(\"ax\");\n"
                            "  ay: assert final (0) else $display(\"ay\");\n"
                            "  initial $assertoff(0, t.i);\n"
                            "endmodule\n"),
            "ax ay u.a1 u.a2 ");
}

TEST(AssertScopeControlSim,
     AProgramInstanceInTheListControlsItsAssertionsAlone) {
  EXPECT_EQ(
      ControlledLines("program P;\n"
                      "  initial ap: assert final (0) else $display(\"p\");\n"
                      "endprogram\n"
                      "module sub;\n"
                      "  a1: assert final (0) else $display(\"u.a1\");\n"
                      "  a2: assert final (0) else $display(\"u.a2\");\n"
                      "endmodule\n"
                      "module t;\n"
                      "  sub u();\n"
                      "  P p();\n"
                      "  ax: assert final (0) else $display(\"ax\");\n"
                      "  ay: assert final (0) else $display(\"ay\");\n"
                      "  initial $assertoff(0, t.p);\n"
                      "endmodule\n"),
      "ax ay u.a1 u.a2 ");
}

TEST(AssertScopeControlSim,
     ACheckerInstanceInTheListControlsItsAssertionsAlone) {
  EXPECT_EQ(ControlledLines("checker C;\n"
                            "  ac: assert final (0) else $display(\"c\");\n"
                            "endchecker\n"
                            "module sub;\n"
                            "  a1: assert final (0) else $display(\"u.a1\");\n"
                            "  a2: assert final (0) else $display(\"u.a2\");\n"
                            "endmodule\n"
                            "module t;\n"
                            "  sub u();\n"
                            "  C c();\n"
                            "  ax: assert final (0) else $display(\"ax\");\n"
                            "  ay: assert final (0) else $display(\"ay\");\n"
                            "  initial $assertoff(0, t.c);\n"
                            "endmodule\n"),
            "ax ay u.a1 u.a2 ");
}

TEST(AssertScopeControlSim, ANamedBlockInTheListControlsItsAssertionsAlone) {
  EXPECT_EQ(ControlledLines("module sub;\n"
                            "  a1: assert final (0) else $display(\"u.a1\");\n"
                            "  a2: assert final (0) else $display(\"u.a2\");\n"
                            "endmodule\n"
                            "module t;\n"
                            "  sub u();\n"
                            "  initial begin : nb\n"
                            "    #1 assert (0) else $display(\"nb\");\n"
                            "  end\n"
                            "  ax: assert final (0) else $display(\"ax\");\n"
                            "  ay: assert final (0) else $display(\"ay\");\n"
                            "  initial $assertoff(0, t.nb);\n"
                            "endmodule\n"),
            "ax ay u.a1 u.a2 ");
}

}  // namespace
