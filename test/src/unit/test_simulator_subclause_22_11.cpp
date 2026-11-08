#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "preprocessor/preprocessor.h"

namespace {

TEST(PragmaSimulation, InterleavedPragmasDoNotChangeResult) {
  auto with = PreprocessAndGet(
      "`pragma unknown_outer\n"
      "module t;\n"
      "  `pragma unknown_before_decl mode = fast\n"
      "  logic [7:0] result;\n"
      "  `pragma unknown_before_initial (a, b = 1)\n"
      "  initial begin\n"
      "    result = 8'd40;\n"
      "    `pragma unknown_between_statements\n"
      "    result = result + 8'd37;\n"
      "  end\n"
      "  `pragma unknown_before_endmodule \"note\"\n"
      "endmodule\n"
      "`pragma unknown_trailing\n",
      "result");
  auto without = PreprocessAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd40;\n"
      "    result = result + 8'd37;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(with, 77u);
  EXPECT_EQ(with, without);
}

TEST(PragmaSimulation, PragmaTextIsNotInterpretedAsSource) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  `pragma unknown_p endmodule, module, wire = result\n"
      "  initial result = 8'd123;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 123u);
}

TEST(PragmaSimulation, PragmaBetweenParameterAndUse) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  parameter P = 8'd21;\n"
      "  `pragma unknown_p encoding = ( style = onehot , depth = 3 )\n"
      "  logic [7:0] result;\n"
      "  initial result = P * 2;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(PragmaSimulation, PragmaDoesNotDisturbNeighbouringDirectiveState) {
  auto result = PreprocessAndGet(
      "`default_nettype none\n"
      "`pragma unknown_p mode = strict\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd55;\n"
      "endmodule\n",
      "result", CuPropagation::kDefaultNetType);
  EXPECT_EQ(result, 55u);
}

TEST(PragmaSimulation, PragmasInConditionalBranchesDrivenEndToEnd) {
  SimFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "`define USE_FAST\n"
                           "module t;\n"
                           "  logic [7:0] result;\n"
                           "`ifdef USE_FAST\n"
                           "  `pragma unknown_fast mode = fast\n"
                           "  initial result = 8'd11;\n"
                           "`else\n"
                           "  `pragma 999 this is not a pragma at all\n"
                           "  initial result = 8'd22;\n"
                           "`endif\n"
                           "endmodule\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = RunPreprocessedSim(f, fid, "result", pp);
  EXPECT_EQ(result, 11u);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PragmaSimulation, PragmaInsideFunctionBodyDoesNotChangeResult) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  function automatic logic [7:0] add_three(input logic [7:0] a);\n"
      "    `pragma unknown_in_function style = inline\n"
      "    add_three = a + 8'd3;\n"
      "  endfunction\n"
      "  initial result = add_three(8'd39);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(PragmaSimulation, MacroSuppliedPragmaExpressionsConsumed) {
  auto result = PreprocessAndGet(
      "`define PRAGMA_ARGS style = onehot, depth = 3\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  `pragma unknown_p `PRAGMA_ARGS\n"
      "  initial result = 8'd7;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 7u);
}

}  // namespace
