#include <gtest/gtest.h>

#include <string>

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

static std::string RunPragma(const std::string& src) {
  SimFixture f;
  return PreprocessAndCapture(src, f);
}

TEST(PragmaSimulation, UnknownPragmaInsideATaskBody) {
  EXPECT_EQ(RunPragma("module t;\n"
                      "  task show(input int v);\n"
                      "    `pragma unknown_in_task\n"
                      "    $display(\"%0d\", v + 1);\n"
                      "  endtask\n"
                      "  initial show(6);\n"
                      "endmodule\n"),
            "7\n");
}

TEST(PragmaSimulation, UnknownPragmaInsideAMultiLineExpression) {
  EXPECT_EQ(RunPragma("module t;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    r = 2 +\n"
                      "`pragma unknown_mid_expr\n"
                      "    3;\n"
                      "    $display(\"%0d\", r);\n"
                      "  end\n"
                      "endmodule\n"),
            "5\n");
}

TEST(PragmaSimulation, UnknownPragmaBesideACompilationUnitDeclaration) {
  EXPECT_EQ(RunPragma("`pragma unknown_unit\n"
                      "int g = 4;\n"
                      "`pragma unknown_unit_after\n"
                      "module t;\n"
                      "  initial $display(\"%0d\", g);\n"
                      "endmodule\n"),
            "4\n");
}

TEST(PragmaSimulation, UnknownPragmaInsideAnInterfaceBody) {
  EXPECT_EQ(RunPragma("interface i;\n"
                      "  `pragma unknown_in_interface\n"
                      "  int v = 8;\n"
                      "endinterface\n"
                      "module t;\n"
                      "  i u();\n"
                      "  initial #1 $display(\"%0d\", u.v);\n"
                      "endmodule\n"),
            "8\n");
}

TEST(PragmaSimulation, UnknownPragmaInsideAProgramBody) {
  EXPECT_EQ(RunPragma("program p;\n"
                      "  `pragma unknown_in_program\n"
                      "  int v = 9;\n"
                      "  initial $display(\"%0d\", v);\n"
                      "endprogram\n"
                      "module t;\n"
                      "  p u();\n"
                      "endmodule\n"),
            "9\n");
}

TEST(PragmaSimulation, UnknownPragmaInsideAClassBody) {
  EXPECT_EQ(RunPragma("class c;\n"
                      "  `pragma unknown_in_class\n"
                      "  int m = 11;\n"
                      "endclass\n"
                      "module t;\n"
                      "  c o;\n"
                      "  initial begin\n"
                      "    o = new;\n"
                      "    $display(\"%0d\", o.m);\n"
                      "  end\n"
                      "endmodule\n"),
            "11\n");
}

TEST(PragmaSimulation, UnknownPragmaInsideACheckerBody) {
  EXPECT_EQ(RunPragma("checker k;\n"
                      "  `pragma unknown_in_checker\n"
                      "  initial assert #0 (1) $display(\"checked\");\n"
                      "endchecker\n"
                      "module t;\n"
                      "  k u();\n"
                      "endmodule\n"),
            "checked\n");
}

}  // namespace
