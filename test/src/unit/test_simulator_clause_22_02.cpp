#include "helpers_preprocess_and_get.h"

TEST(CompilerDirectiveSimulation, DirectiveCanBeOverridden) {
  auto result = PreprocessAndGet(
      "`define X 8'd10\n"
      "`define X 8'd20\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `X;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 20u);
}

TEST(CompilerDirectiveSimulation,
     DirectiveInConditionalBlockAffectsSimulation) {
  auto result = PreprocessAndGet(
      "`define FEATURE 1\n"
      "`ifdef FEATURE\n"
      "`define VAL 8'd42\n"
      "`else\n"
      "`define VAL 8'd0\n"
      "`endif\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(CompilerDirectiveSimulation, DirectiveInCommentDoesNotAffectSimulation) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd42\n"
      "// `define VAL 8'd99\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(CompilerDirectiveSimulation,
     MacroExpansionWithinDirectiveAffectsSimulation) {
  auto result = PreprocessAndGet(
      "`define INNER 8'd77\n"
      "`define OUTER `INNER\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `OUTER;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 77u);
}
