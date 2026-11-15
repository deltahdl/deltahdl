#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string CheckerOverB(const std::string& body, int end) {
  return "checker chk(int b, logic clk);\n" + body +
         "endchecker\n"
         "module top;\n"
         "  logic clk = 0;\n"
         "  int b = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) b = b + 1;\n"
         "  chk c(b, clk);\n"
         "  initial #" +
         std::to_string(end) +
         " $finish;\n"
         "endmodule\n";
}

TEST(CheckerProcedures, AlwaysFfReadsSampledValues) {
  SimFixture f;
  auto* z = RunAndFindVar(CheckerOverB("  int z, v, x;\n"
                                       "  assign x = b;\n"
                                       "  always_ff @(posedge clk) z <= b;\n"
                                       "  always_comb v = b;\n",
                                       42),
                          f, "c.z");
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(z->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("c.v")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("c.x")->value.ToUint64(), 4u);
}

TEST(CheckerProcedures, AlwaysFfImmediateAssertionReadsSampledValues) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      CheckerOverB("  int pass = 0, fail = 0;\n"
                   "  always_ff @(posedge clk) begin\n"
                   "    a1: assert (b % 2 == 0) pass++; else fail++;\n"
                   "  end\n",
                   32),
      f, "c.pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 1u);
}

}  // namespace
