#include <gtest/gtest.h>

#include <string_view>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

namespace {

TEST(EventTriggerSimulator, NonblockingTriggerUnblocksWaiter) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    result = 77;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 ->> ev;\n"
      "    #2 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(EventTriggerSimulator, NonblockingTriggerWithDelay) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    result = 88;\n"
      "  end\n"
      "  initial begin\n"
      "    ->> #10 ev;\n"
      "    #20 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(EventTriggerSimulator, NonblockingTriggerDefersToNbaRegion) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    ->> ev;\n"
      "    @(ev);\n"
      "    result = 99;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(EventTriggerSimulator, BlockingTriggerIsOneShotAndLost) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = 7;\n"
      "    -> ev;\n"
      "    @(ev);\n"
      "    result = 42;\n"
      "  end\n"
      "  initial #100 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(EventTriggerSimulator, BlockingTriggerHierarchicalTarget) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module sub;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    @(ev);\n"
      "    result = 9;\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  sub s();\n"
      "  initial begin\n"
      "    #5 -> s.ev;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "s.result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

TEST(EventTriggerSimulator, NonblockingTriggerHierarchicalTarget) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module sub;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    @(ev);\n"
      "    result = 9;\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  sub s();\n"
      "  initial begin\n"
      "    #5 ->> s.ev;\n"
      "    #2 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "s.result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

TEST(EventTriggerSimulator, NonblockingTriggerCoexistsWithNonblockingAssign) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] x, result;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    result = 0;\n"
      "    @(ev);\n"
      "    result = x;\n"
      "  end\n"
      "  initial begin\n"
      "    x <= 5;\n"
      "    ->> ev;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(EventTriggerSimulator, TriggerUnblocksMultipleWaiters) {
  LowerFixture f;
  auto [a, b] = RunModuleTwoVars(f,
                                 "module t;\n"
                                 "  event ev;\n"
                                 "  logic [7:0] a, b;\n"
                                 "  initial begin\n"
                                 "    @(ev);\n"
                                 "    a = 8'd11;\n"
                                 "  end\n"
                                 "  initial begin\n"
                                 "    @(ev);\n"
                                 "    b = 8'd22;\n"
                                 "  end\n"
                                 "  initial begin\n"
                                 "    #5 -> ev;\n"
                                 "    #1 $finish;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "a", "b");
  EXPECT_EQ(a, 11u);
  EXPECT_EQ(b, 22u);
}

TEST(EventTriggerSimulator, NonblockingTriggerWaitsForEventControl) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic clk;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    result = 55;\n"
      "  end\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    clk = 0;\n"
      "    ->> @(posedge clk) ev;\n"
      "    #5 clk = 1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(EventTriggerSimulator, NonblockingTriggerGatedOnEventControl) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic clk;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    result = 55;\n"
      "  end\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    clk = 0;\n"
      "    ->> @(posedge clk) ev;\n"
      "    #10 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventTriggerSimulator, NonblockingTriggerRepeatEventControl) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic clk;\n"
      "  logic [31:0] result, mid;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    result = 55;\n"
      "  end\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    clk = 0;\n"
      "    ->> repeat(2) @(posedge clk) ev;\n"
      "    #5 clk = 1;\n"
      "    #2 clk = 0;\n"
      "    #2 mid = result;\n"
      "    #2 clk = 1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* mid = f.ctx.FindVariable("mid");
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(mid, nullptr);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(mid->value.ToUint64(), 0u);
  EXPECT_EQ(result->value.ToUint64(), 55u);
}

TEST(NamedEventSim, EventPassedToAnInputFormalIsTheCallersEvent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event done, e;\n"
      "  int t1, t2, r;\n"
      "  task trigger(event ev); -> ev; endtask\n"
      "  task waiter(event ev); @ev; t2 = $time; endtask\n"
      "  initial begin\n"
      "    fork\n"
      "      begin @done; t1 = $time; end\n"
      "      #1 trigger(done);\n"
      "      waiter(e);\n"
      "      #2 -> e;\n"
      "    join\n"
      "    r = t1 * 10 + t2;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(NamedEventSim, LoopGenerateEventTriggeredByItsPath) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int at;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    event e;\n"
      "  end\n"
      "  initial fork\n"
      "    begin @g[1].e; at = $time; end\n"
      "    #2 -> g[1].e;\n"
      "  join\n"
      "endmodule\n",
      f, "at");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(NamedEventSim, EventArrayElementsAreEventsOfTheirOwn) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event arr[2];\n"
      "  event m[string];\n"
      "  int t1, t2, r;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin @(arr[1]); t1 = $time; end\n"
      "      begin #1 -> arr[0]; #1 -> arr[1]; end\n"
      "    join\n"
      "    fork\n"
      "      begin @(m[\"k\"]); t2 = $time; end\n"
      "      #2 -> m[\"k\"];\n"
      "    join\n"
      "    r = t1 * 10 + t2;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 24u);
}

TEST(NamedEventSim, ChangingAnEventArrayIndexMakesNoEventOccur) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev[2];\n"
      "  event grid[2][2];\n"
      "  int i, j, k, n, hits;\n"
      "  initial begin @(ev[i]); hits += 1; end\n"
      "  initial begin @(grid[j][k]); hits += 10; end\n"
      "  initial begin @(ev[n]); hits += 100; end\n"
      "  initial begin #1 i = 1; #1 j = 1; #1 k = 1; #1 n <= 1; end\n"
      "  initial #10 $finish;\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(NamedEventSim, TriggeringTheIndexedEventArrayElementWakesTheWaiter) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev[2];\n"
      "  event grid[2][2];\n"
      "  int i = 1, j = 1, k = 0, a, b, r;\n"
      "  initial begin @(ev[i]); a = $time; end\n"
      "  initial begin @(grid[j][k]); b = $time; end\n"
      "  initial begin #2 -> ev[1]; #1 -> grid[1][0]; end\n"
      "  initial #10 r = a * 10 + b;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 23u);
}

TEST(NamedEventSim, MultidimensionalEventArrayLeavesAreEvents) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event grid[2][3];\n"
      "  int j = 1, k = 2, a, b, c, r;\n"
      "  initial begin @(grid[1][2]); a = $time; end\n"
      "  initial begin #2 wait (grid[0][1].triggered); b = $time; end\n"
      "  initial begin @(grid[1][1]); c = 9; end\n"
      "  initial begin #1 -> grid[j][k]; #1 -> grid[0][1]; end\n"
      "  initial #10 r = a * 10 + b + c;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(EventTriggerSimulator, NonblockingTriggerFiresAnEventArrayElement) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event one[2];\n"
      "  event grid[2][2];\n"
      "  event m[string];\n"
      "  event q[$];\n"
      "  event e;\n"
      "  int i = 1, hits;\n"
      "  initial q.push_back(e);\n"
      "  initial begin @(one[1]); hits += $time == 2 ? 1 : 0; end\n"
      "  initial begin @(grid[1][0]); hits += $time == 2 ? 10 : 0; end\n"
      "  initial begin @(m[\"k\"]); hits += $time == 2 ? 100 : 0; end\n"
      "  initial begin @(e); hits += $time == 2 ? 1000 : 0; end\n"
      "  initial begin\n"
      "    #2 ->> one[i];\n"
      "    ->> grid[1][0];\n"
      "    ->> m[\"k\"];\n"
      "    ->> q[0];\n"
      "  end\n"
      "  initial #10 $finish;\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1111u);
}

TEST(EventTriggerSimulator,
     NonblockingTriggerOfAnElementSetsItsTriggeredState) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event one[2];\n"
      "  int t1;\n"
      "  initial begin #3 wait (one[1].triggered); t1 = $time; end\n"
      "  initial #3 ->> one[1];\n"
      "  initial #10 $finish;\n"
      "endmodule\n",
      f, "t1");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(EventTriggerSimulator, NonblockingTriggerFiresAClassEventProperty) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "class C;\n"
      "  event ev;\n"
      "endclass\n"
      "module t;\n"
      "  C h = new;\n"
      "  int t1;\n"
      "  initial begin @(h.ev); t1 = $time; end\n"
      "  initial #4 ->> h.ev;\n"
      "  initial #10 $finish;\n"
      "endmodule\n",
      f, "t1");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(EventTriggerSimulator, NonblockingTriggerKeepsAWaiterItsIffRefuses) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  bit en;\n"
      "  int t1 = -1;\n"
      "  initial begin @(ev iff en); t1 = $time; end\n"
      "  initial begin #1 ->> ev; #1 en = 1; ->> ev; end\n"
      "  initial #10 $finish;\n"
      "endmodule\n",
      f, "t1");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

}  // namespace
