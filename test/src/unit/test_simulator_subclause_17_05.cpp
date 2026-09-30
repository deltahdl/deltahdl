#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The source both cases share: the module raises b with a blocking
// assignment at every posedge of clk, 5, 15, 25 and 35, and hands it to the
// checker whose body is `body`, the run ending at `end`.
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

// §17.5: an expression of a checker's always_ff other than its event control
// reads sampled values, while an always_comb and a continuous assignment of
// the checker read current ones. At the posedge at 35 the module raises b to
// 4, so z takes the sampled 3 and v and x the 4. z took the 4 as well.
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

// §17.5: the condition of an immediate assertion in a checker's always_ff is
// an expression of it too, so at 5, 15 and 25 it tests the sampled 0, 1 and
// 2, holding twice. It tested the current 1, 2 and 3, holding once.
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
