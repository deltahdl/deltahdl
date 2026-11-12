#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
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

TEST(DefaultClockingSim, ANestedCheckersAssertionTakesTheDefaultClock) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      "module top;\n"
      "  logic clk = 0, a = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "  checker chk(logic x);\n"
      "    int pass = 0, fail = 0;\n"
      "    a1: assert property (x) pass++; else fail++;\n"
      "  endchecker\n"
      "  chk c(a);\n"
      "  initial begin #12 a = 0; #20 a = 1; #20 $finish; end\n"
      "endmodule\n",
      f, "c.pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 2u);
}

TEST(DefaultClockingSim, ANestedModuleCountsItsEnclosingModulesDefault) {
  SimFixture f;
  std::string out = RunCapture(
      "module o(input logic clk);\n"
      "  default clocking co @(posedge clk); endclocking\n"
      "  module n;\n"
      "    initial begin #1 ##1; $display(\"n %0t\", $time); end\n"
      "  endmodule\n"
      "  n un();\n"
      "endmodule\n"
      "module m(input logic clk);\n"
      "  default clocking cm @(negedge clk); endclocking\n"
      "endmodule\n"
      "module t;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  o uo(clk);\n"
      "  m um(clk);\n"
      "  initial #20 $finish;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "n 5\n$finish at time 20\n");
}

TEST(DefaultClockingSim, ANestedInterfaceCountsItsEnclosingModulesDefault) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  logic clk = 0;\n"
                 "  always #5 clk = ~clk;\n"
                 "  default clocking cb @(posedge clk); endclocking\n"
                 "  interface ifc;\n"
                 "    initial begin ##2 $display(\"if %0t\", $time); end\n"
                 "  endinterface\n"
                 "  ifc u();\n"
                 "  initial #40 $finish;\n"
                 "endmodule\n",
                 f),
      "if 15\n$finish at time 40\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DefaultClockingSim, TheClauseProgramCountsItsDefaultBlocksEvents) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("program test(input logic clk, input logic [15:0] data);\n"
                 "  default clocking bus @(posedge clk);\n"
                 "    inout data;\n"
                 "  endclocking\n"
                 "  initial begin\n"
                 "    ## 5;\n"
                 "    if (bus.data == 10)\n"
                 "      ## 1;\n"
                 "    else\n"
                 "      ## 3;\n"
                 "    $display(\"%0t %0d\", $time, bus.data);\n"
                 "  end\n"
                 "endprogram\n"
                 "module top;\n"
                 "  logic clk = 0;\n"
                 "  logic [15:0] data = 0;\n"
                 "  always #5 clk = ~clk;\n"
                 "  initial #42 data = 10;\n"
                 "  test t(clk, data);\n"
                 "endmodule\n",
                 f),
      "55 10\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
