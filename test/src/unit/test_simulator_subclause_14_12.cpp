#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast_stmt.h"
#include "simulator/clocking.h"

using namespace delta;

namespace {

TEST(DefaultClockingSim, SetAndGetDefaultClocking) {
  ClockingManager cmgr;
  EXPECT_TRUE(cmgr.GetDefaultClocking().empty());

  ClockingBlock block;
  block.name = "sys_cb";
  block.clock_signal = "sys_clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{1};
  block.default_output_skew = SimTime{2};
  cmgr.Register(block);

  cmgr.SetDefaultClocking("sys_cb");
  EXPECT_EQ(cmgr.GetDefaultClocking(), "sys_cb");

  const auto* found = cmgr.Find("sys_cb");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->default_input_skew.ticks, 1u);
  EXPECT_EQ(found->default_output_skew.ticks, 2u);
}

// §14.3 (printed page 355) makes the identifier of the default clocking
// optional, and §14.12 has `##` count the default's events in its scope, so
// `##3` waits for the posedges at 5, 15 and 25. The unnamed block had no name
// to be registered under, was no default, and `##3` ran on at 0.
TEST(DefaultClockingSim, UnnamedDefaultClockingBlockClocksCycleDelays) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic [7:0] d = 1;\n"
      "  default clocking @(posedge clk);\n"
      "    input d;\n"
      "  endclocking\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin ##3; $display(\"%0t\", $time); $finish; end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "25\n$finish at time 25\n");
}

// §14.12 (printed page 362), its Example 2: `default clocking busB;` makes
// the block declared as busB the default, so `##2` counts busB's negedges at
// 10 and 20 rather than busA's posedges. It declared nothing and made no
// block the default, and `##2` ran on at 0.
TEST(DefaultClockingSim, DefaultClockingByNameClocksCycleDelays) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic [7:0] d = 1;\n"
      "  clocking busA @(posedge clk); input d; endclocking\n"
      "  clocking busB @(negedge clk); input d; endclocking\n"
      "  default clocking busB;\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin ##2; $display(\"%0t\", $time); $finish; end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "20\n$finish at time 20\n");
}

// §14.12 (printed page 361): a default clocking is the default within its own
// module, so t's `##1` counts t's posedges and m's counts m's negedges, each
// from time 1. The design kept one default, the last instance's, and t's
// `##1` waited for m's negedge at 10.
TEST(DefaultClockingSim, EachModuleCountsItsOwnDefaultClocking) {
  SimFixture f;
  std::string out = RunCapture(
      "module m(input logic clk);\n"
      "  default clocking cm @(negedge clk); endclocking\n"
      "  initial begin #1 ##1; $display(\"m %0t\", $time); end\n"
      "endmodule\n"
      "module t;\n"
      "  logic clk = 0;\n"
      "  default clocking ct @(posedge clk); endclocking\n"
      "  always #5 clk = ~clk;\n"
      "  m u(clk);\n"
      "  initial begin #1 ##1; $display(\"t %0t\", $time); #20 $finish; end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "t 5\nm 10\n$finish at time 25\n");
}

}  // namespace
