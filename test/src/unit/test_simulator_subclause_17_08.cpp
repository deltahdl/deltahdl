#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(CheckerFreeActualRuns, AFunctionReceivesTheFreeVariablesValue) {
  SimFixture f;
  auto* fail = RunAndFindVar(
      "checker chk(logic clk);\n"
      "  function automatic bit [7:0] f(bit [7:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  rand bit [7:0] r;\n"
      "  m1: assume property (@(posedge clk) r != 8'd0);\n"
      "  bit [7:0] y = 8'd0, z = 8'd1;\n"
      "  int pass = 0, fail = 0, differ = 0;\n"
      "  always_ff @(posedge clk) begin\n"
      "    z <= f(r);\n"
      "    y <= r;\n"
      "    if (z != y) differ <= differ + 1;\n"
      "  end\n"
      "  a1: assert property (@(posedge clk) f(r) == r) pass++; else fail++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(clk);\n"
      "  initial #52 $finish;\n"
      "endmodule\n",
      f, "c.fail");
  ASSERT_NE(fail, nullptr);
  EXPECT_EQ(fail->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("c.pass")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("c.differ")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("c.z")->value.ToUint64(),
            f.ctx.FindVariable("c.y")->value.ToUint64());
  EXPECT_NE(f.ctx.FindVariable("c.y")->value.ToUint64(), 0u);
}

}  // namespace
