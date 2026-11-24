#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PastSim, EachVariableOfTheExpressionTakesItsOwnInitialValue) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      "module m;\n"
      "  logic clk = 0;\n"
      "  logic [3:0] d = 5;\n"
      "  bit [3:0] b;\n"
      "  wire w = 1;\n"
      "  int pass = 0, fail = 0;\n"
      "  assert property (@(posedge clk) $past(d + b) == 4'd5 &&\n"
      "                   $past(w) === 1'bz) pass++; else fail++;\n"
      "  initial begin\n"
      "    #1 d = 9; b = 2;\n"
      "    #4 clk = 1; #5 clk = 0;\n"
      "  end\n"
      "endmodule\n",
      f, "pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fail")->value.ToUint64(), 0u);
}

}  // namespace
