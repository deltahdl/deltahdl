#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast_stmt.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(GlobalClockingSim, SetAndGetGlobalClocking) {
  ClockingManager cmgr;
  EXPECT_TRUE(cmgr.GetGlobalClocking().empty());

  ClockingBlock block;
  block.name = "gclk";
  block.clock_signal = "clk_global";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  block.is_global = true;
  cmgr.Register(block);

  cmgr.SetGlobalClocking("gclk");
  EXPECT_EQ(cmgr.GetGlobalClocking(), "gclk");

  const auto* found = cmgr.Find("gclk");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_global);
}

TEST(GlobalClockingSim, GlobalAndDefaultCoexist) {
  ClockingManager cmgr;

  ClockingBlock gblock;
  gblock.name = "gclk";
  gblock.clock_signal = "sys_clk";
  gblock.clock_edge = Edge::kPosedge;
  gblock.is_global = true;
  cmgr.Register(gblock);
  cmgr.SetGlobalClocking("gclk");

  ClockingBlock dblock;
  dblock.name = "dclk";
  dblock.clock_signal = "bus_clk";
  dblock.clock_edge = Edge::kPosedge;
  cmgr.Register(dblock);
  cmgr.SetDefaultClocking("dclk");

  EXPECT_EQ(cmgr.GetGlobalClocking(), "gclk");
  EXPECT_EQ(cmgr.GetDefaultClocking(), "dclk");
  EXPECT_NE(cmgr.Find("gclk"), nullptr);
  EXPECT_NE(cmgr.Find("dclk"), nullptr);
}

TEST(GlobalClockingSim, EveryDeclaredPosedgeRunsTheGlobalClockEventBody) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
}

TEST(GlobalClockingSim, NegedgeDeclarationMakesGlobalClockFireOnFallsOnly) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b1;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(negedge clk); endclocking\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
}

TEST(GlobalClockingSim, GlobalClockInAnInitialEventControlResumesThatProcess) {
  SimFixture f;
  auto* done = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  logic done = 1'b0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  initial @($global_clock) done = 1'b1;\n"
      "  initial #5 clk = 1'b1;\n"
      "endmodule\n",
      f, "done");
  ASSERT_NE(done, nullptr);
  EXPECT_EQ(done->value.ToUint64(), 1u);
}

TEST(GlobalClockingSim,
     GlobalClockInAnAssertionFailStatementResumesThatProcess) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  logic ok = 1'b0;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  initial assert (ok) else @($global_clock) hits = hits + 1;\n"
      "  initial #5 clk = 1'b1;\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
}

TEST(GlobalClockingSim,
     GlobalClockInAnAssertionPassStatementResumesThatProcess) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  logic ok = 1'b1;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  initial assert (ok) @($global_clock) hits = hits + 1;\n"
      "  initial #5 clk = 1'b1;\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
}

TEST(GlobalClockingSim, GlobalClockInARandcaseItemResumesThatProcess) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  initial randcase 1: @($global_clock) hits = hits + 1; endcase\n"
      "  initial #5 clk = 1'b1;\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
}

TEST(GlobalClockingSim, GlobalClockInAChildFollowsItsAncestorsDeclaration) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module common_sub;\n"
      "  int hits = 0;\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "endmodule\n"
      "module subsystem1;\n"
      "  logic subclk1 = 1'b0;\n"
      "  global clocking sub_sys1 @(posedge subclk1); endclocking\n"
      "  common_sub common();\n"
      "  initial begin\n"
      "    #5 subclk1 = 1'b1;\n"
      "    #5 subclk1 = 1'b0;\n"
      "    #5 subclk1 = 1'b1;\n"
      "    #5 subclk1 = 1'b0;\n"
      "    #5 subclk1 = 1'b1;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  subsystem1 sub1();\n"
      "endmodule\n",
      f, "sub1.common.hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
}

TEST(GlobalClockingSim,
     SiblingInstancesEachFollowTheirOwnAncestorsDeclaration) {
  SimFixture f;
  const std::string kSrc =
      "module common_sub;\n"
      "  int hits = 0;\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "endmodule\n"
      "module subsystem1;\n"
      "  logic subclk1 = 1'b0;\n"
      "  global clocking sub_sys1 @(posedge subclk1); endclocking\n"
      "  common_sub common();\n"
      "  initial #5 subclk1 = 1'b1;\n"
      "endmodule\n"
      "module subsystem2;\n"
      "  logic subclk2 = 1'b0;\n"
      "  global clocking sub_sys2 @(posedge subclk2); endclocking\n"
      "  common_sub common();\n"
      "  initial begin\n"
      "    #5 subclk2 = 1'b1;\n"
      "    #5 subclk2 = 1'b0;\n"
      "    #5 subclk2 = 1'b1;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  subsystem1 sub1();\n"
      "  subsystem2 sub2();\n"
      "endmodule\n";
  auto* first = RunAndFindVar(kSrc, f, "sub1.common.hits");
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(first->value.ToUint64(), 1u);
  auto* second = f.ctx.FindVariable("sub2.common.hits");
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(second->value.ToUint64(), 2u);
}

TEST(GlobalClockingSim, AChildsOwnGlobalClockingBeatsItsAncestors) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module child;\n"
      "  logic ownclk = 1'b0;\n"
      "  int hits = 0;\n"
      "  global clocking own_gclk @(posedge ownclk); endclocking\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "  initial begin\n"
      "    #10 ownclk = 1'b1;\n"
      "    #10 ownclk = 1'b0;\n"
      "    #10 ownclk = 1'b1;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  logic topclk = 1'b0;\n"
      "  global clocking top_gclk @(posedge topclk); endclocking\n"
      "  child c();\n"
      "  initial begin\n"
      "    #3 topclk = 1'b1;\n"
      "    #3 topclk = 1'b0;\n"
      "    #3 topclk = 1'b1;\n"
      "    #3 topclk = 1'b0;\n"
      "    #3 topclk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "c.hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
}

TEST(GlobalClockingSim, TopLevelGlobalClockingReachesAReferenceInAChild) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module child;\n"
      "  logic clk = 1'b0;\n"
      "  int hits = 0;\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 1'b0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  child c();\n"
      "  initial begin\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "c.hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
}

TEST(GlobalClockingSim,
     ChildFollowsTheTopsGlobalClockNotItsOwnLikeNamedSignal) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module child;\n"
      "  logic clk = 1'b0;\n"
      "  int hits = 0;\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "  initial begin\n"
      "    #7 clk = 1'b1;\n"
      "    #7 clk = 1'b0;\n"
      "    #7 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 1'b0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  child c();\n"
      "  initial begin\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "c.hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
}

TEST(GlobalClockingSim,
     ReferenceInTheDeclaringTopModuleStaysUnqualifiedAlongsideAChild) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module child;\n"
      "  logic clk = 1'b0;\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 1'b0;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  child c();\n"
      "  always @($global_clock) hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
}

TEST(GlobalClockingSim, GlobalClockInATaskBodyNamesTheDeclaringScopesEvent) {
  SimFixture f;
  auto* design = ElaborateSrcAllTops(
      "module another_module;\n"
      "  logic another_clk = 0;\n"
      "  int t_at, tk_at;\n"
      "  global clocking another_clocking @(posedge another_clk);\n"
      "  endclocking\n"
      "  initial #6 another_clk = 1;\n"
      "  task t(); @($global_clock); t_at = $time; endtask\n"
      "  task tk(); @($global_clock); tk_at = $time; endtask\n"
      "  initial tk();\n"
      "endmodule\n"
      "module subsystem1;\n"
      "  logic subclk1 = 0;\n"
      "  global clocking sub_sys1 @(posedge subclk1); endclocking\n"
      "  initial #3 subclk1 = 1;\n"
      "  initial another_module.t();\n"
      "  initial #10 $finish;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  LowerRunAndCheck(f, design,
                   {{"another_module.tk_at", 6u}, {"another_module.t_at", 6u}});
}

TEST(GlobalClockingSim, ADeclaredGlobalClockResolvesWhereTheInstanceIs) {
  SimFixture f;
  std::string out = RunCapture(
      "package pk;\n"
      "  property p(x); @($global_clock) x; endproperty\n"
      "endpackage\n"
      "module sub(input logic c);\n"
      "  import pk::*;\n"
      "  int n;\n"
      "  global clocking @(posedge c); endclocking\n"
      "  assert property (p(1'b1)) n++;\n"
      "endmodule\n"
      "module own(input logic c);\n"
      "  int n;\n"
      "  global clocking @(posedge c); endclocking\n"
      "  property q(x); @($global_clock) x; endproperty\n"
      "  assert property (q(1'b1)) n++;\n"
      "endmodule\n"
      "module m;\n"
      "  logic fast = 0, slow = 0;\n"
      "  always #5 fast = ~fast;\n"
      "  always #10 slow = ~slow;\n"
      "  global clocking @(posedge fast); endclocking\n"
      "  sub s1(fast);\n"
      "  sub s2(slow);\n"
      "  own o(slow);\n"
      "  initial #42 begin\n"
      "    $display(\"%0d %0d %0d\", s1.n, s2.n, o.n);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("4 2 2\n"), std::string::npos) << out;
}

TEST(GlobalClockingSim, AGlobalClockInAnInstanceActualResolvesAtTheAssertion) {
  SimFixture f;
  std::string out = RunCapture(
      "module sub(input logic c);\n"
      "  logic a = 1;\n"
      "  int k, j, u, w;\n"
      "  global clocking @(posedge c); endclocking\n"
      "  property r(sequence s); s; endproperty\n"
      "  sequence q(sequence s); s; endsequence\n"
      "  assert property (r(@$global_clock a)) k++;\n"
      "  cover property (q(@($global_clock) a)) j++;\n"
      "  assume property (r(@($global_clock) a)) u++;\n"
      "  initial assert property (q(@$global_clock a)) w++;\n"
      "endmodule\n"
      "module m;\n"
      "  logic fast = 0, slow = 0;\n"
      "  always #5 fast = ~fast;\n"
      "  always #10 slow = ~slow;\n"
      "  sub s1(fast);\n"
      "  sub s2(slow);\n"
      "  initial #42 begin\n"
      "    $display(\"%0d %0d %0d %0d\", s1.k, s1.j, s1.u, s1.w);\n"
      "    $display(\"%0d %0d %0d %0d\", s2.k, s2.j, s2.u, s2.w);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("4 4 4 1\n2 2 2 1\n"), std::string::npos) << out;
}

TEST(GlobalClockingSim, AGlobalClockInACheckerActualResolvesInTheChecker) {
  SimFixture f;
  std::string out = RunCapture(
      "checker chk(sequence s, logic cclk);\n"
      "  int n;\n"
      "  global clocking @(posedge cclk); endclocking\n"
      "  cover property (s) n++;\n"
      "endchecker\n"
      "module m;\n"
      "  logic fast = 0, slow = 0, a = 1;\n"
      "  always #5 fast = ~fast;\n"
      "  always #10 slow = ~slow;\n"
      "  global clocking @(posedge fast); endclocking\n"
      "  chk c(@$global_clock a [*1:$] ##1 a, slow);\n"
      "  initial #42 begin\n"
      "    $display(\"n=%0d\", c.n);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1\n"), std::string::npos) << out;
}

TEST(GlobalClockingSim,
     AnOrEventInterfaceChildAndNestedCheckerFollowTheirDeclarations) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface leaf;\n"
                       "  int n;\n"
                       "  always @($global_clock) n++;\n"
                       "endinterface\n"
                       "interface bus(input logic c);\n"
                       "  global clocking @(posedge c); endclocking\n"
                       "  leaf l();\n"
                       "endinterface\n"
                       "checker inner_ck;\n"
                       "  int n = 0;\n"
                       "  always_ff @($global_clock) n <= n + 1;\n"
                       "endchecker\n"
                       "checker outer_ck(logic c);\n"
                       "  global clocking @(negedge c); endclocking\n"
                       "  inner_ck i();\n"
                       "endchecker\n"
                       "module top;\n"
                       "  logic clk1 = 0, clk2 = 0;\n"
                       "  always #5 clk1 = ~clk1;\n"
                       "  initial #2 forever #10 clk2 = ~clk2;\n"
                       "  global clocking sys @(clk1 or clk2); endclocking\n"
                       "  int n;\n"
                       "  always @($global_clock) n++;\n"
                       "  bus b(clk1);\n"
                       "  outer_ck oc(clk1);\n"
                       "  initial #41 begin $display(\"%0d %0d %0d\", n, "
                       "b.l.n, oc.i.n); $finish; end\n"
                       "endmodule\n",
                       f),
            "11 4 4\n$finish at time 41\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(GlobalClockingSim,
     DISABLED_ADeclaredSequenceOnTheGlobalClockResolvesWhereItIsUsed) {
  SimFixture f;
  std::string out = RunCapture(
      "package pk;\n"
      "  sequence s(x); @($global_clock) x; endsequence\n"
      "endpackage\n"
      "module sub(input logic c);\n"
      "  import pk::*;\n"
      "  int a, cp, cs, imp, ng, sq, pr;\n"
      "  global clocking @(posedge c); endclocking\n"
      "  assert property (s(1'b1)) a++;\n"
      "  cover property (s(1'b1)) cp++;\n"
      "  cover sequence (s(1'b1)) cs++;\n"
      "  property pimp; s(1'b1) |-> 1'b1; endproperty\n"
      "  property png; not s(1'b0); endproperty\n"
      "  sequence ssq; s(1'b1) ##1 1'b1; endsequence\n"
      "  assert property (pimp) imp++;\n"
      "  assert property (png) ng++;\n"
      "  assert property (ssq) sq++;\n"
      "  initial assert property (s(1'b1)) pr++;\n"
      "endmodule\n"
      "module own(input logic c);\n"
      "  int a;\n"
      "  global clocking @(posedge c); endclocking\n"
      "  sequence t(x); @($global_clock) x; endsequence\n"
      "  assert property (t(1'b1)) a++;\n"
      "endmodule\n"
      "module m;\n"
      "  logic fast = 0, slow = 0;\n"
      "  always #5 fast = ~fast;\n"
      "  always #10 slow = ~slow;\n"
      "  global clocking @(posedge fast); endclocking\n"
      "  sub s1(fast);\n"
      "  sub s2(slow);\n"
      "  own o(slow);\n"
      "  initial #42 begin\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", s1.a, s1.cp, s1.cs, "
      "s1.imp, s1.ng, s1.sq, s1.pr);\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", s2.a, s2.cp, s2.cs, "
      "s2.imp, s2.ng, s2.sq, s2.pr);\n"
      "    $display(\"%0d\", o.a);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("4 4 4 4 4 3 1\n2 2 2 2 2 1 1\n2\n"), std::string::npos)
      << out;
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
