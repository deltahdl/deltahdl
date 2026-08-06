// §22.11 `pragma -- the "no effect on the interpretation of the source text"
// rule observed at the far end of the pipeline.
//
// The directive is consumed in src/preprocessor/preprocessor.cpp. These tests
// build real SystemVerilog with unrecognized pragmas interleaved among the
// declarations and statements, run the full preprocess -> parse -> elaborate ->
// lower -> simulate pipeline, and check the simulated values are the ones the
// pragma-free source produces.

#include "helpers_preprocess_and_get.h"

namespace {

// Pragmas placed before the module, inside it, between statements, and after
// endmodule must not change what the design computes.
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

// The directive's own text is not source text: identifiers inside a pragma
// that happen to spell SystemVerilog keywords reach neither the lexer nor the
// elaborator, so the module still ends where endmodule says it does.
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

// A pragma standing between a parameter and the expression that reads it does
// not disturb the value the simulation ends up with.
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

// The `celldefine region and the `default_nettype setting that the later
// stages consume survive a pragma written in the middle of them.
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

// End-to-end over the conditional compilation the pragma rule depends on: a
// pragma in the branch that is compiled in is consumed normally, while a
// malformed one in the branch that is compiled away is never even examined.
// Both facts have to hold for the run to reach the expected value cleanly.
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

// A subroutine body is another syntactic position; a pragma between its
// statements must not change what the function returns.
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

// A pragma supplied by a text macro expansion is still consumed as a directive
// rather than reaching the simulation.
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
