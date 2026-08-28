#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
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

// §14.14: "The $global_clock system function shall be used to explicitly refer
// to the event expression in the effective global clocking declaration", and
// its lookup rule a) resolves that reference against the global clocking
// declaration in the enclosing module instance. The three cases below
// elaborate, lower and run the design, because acceptance is not what §14.14
// requires: the cases in test/src/unit/test_elaborator_subclause_14_14.cpp
// stop at elaboration, where a process that arms no watcher and stays
// suspended at @($global_clock) for the whole run looks exactly like one that
// resumes on every clocking event. Only a value the process wrote separates
// the two, so each case here drives the declared clock and reads that value
// back.
//
// The declaration is on `posedge clk` and the run drives three rises (t=5,
// t=15, t=25) with two falls between them, so the body runs three times. `clk`
// takes its starting level from its declaration rather than from a process, so
// the run contains no transition out of x and the rises above are every posedge
// there is.
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

// §14.14 makes $global_clock the event expression of the effective global
// clocking declaration, so the edge it fires on is the edge that declaration
// names. Here that is `negedge clk`, and the run drives three falls (t=5, t=15,
// t=25) against two rises (t=10, t=20). Three is therefore the count only a
// process following the declared edge reaches: one that fires on the rises
// instead leaves hits at 2, and the case above cannot tell those apart because
// its declaration names posedge.
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

// §14.14 states where $global_clock refers, not where it may be written, so it
// stands in any event control rather than only in the sensitivity list of an
// always. Here it is the event control of a statement in an initial block: the
// rise at t=5 is the clocking event of the declaration found by rule a), and
// the process resumes there and writes done. `done` starts at 0, so a run that
// never resumes the process reads back 0 rather than x.
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

}  // namespace
