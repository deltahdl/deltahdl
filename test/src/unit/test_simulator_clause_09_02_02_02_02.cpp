#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AlwaysCombVsAlwaysStarSim, AlwaysStarNoInputNoExecuteAtTimeZero) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] y;\n"
      "  always @* y = 8'd42;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0u);
}

TEST(AlwaysCombVsAlwaysStarSim, AlwaysStarNotSensitiveToFunctionBodyReads) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] ext, a, result;\n"
      "  function automatic logic [7:0] add_ext(input logic [7:0] x);\n"
      "    return x + ext;\n"
      "  endfunction\n"
      "  always @* result = add_ext(a);\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    ext = 8'd10;\n"
      "    #1 ext = 8'd20;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

}  // namespace
