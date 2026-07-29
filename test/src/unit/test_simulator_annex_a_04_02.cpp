#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(GenerateSimulation, GenerateForAssignValues) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter N = 3) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      logic [31:0] w;\n"
      "      assign w = 10;\n"
      "    end\n"
      "  endgenerate\n"
      "  assign x = 7;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

}  // namespace
