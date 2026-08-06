#include "helpers_preprocess_and_get.h"

TEST(DefineSimulation, ObjectLikeMacroSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd99\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}

TEST(DefineSimulation, FunctionLikeMacroSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`define DOUBLE(x) (x * 2)\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `DOUBLE(8'd7);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 14u);
}

TEST(DefineSimulation, RedefinedMacroUsesLatestValueForSimulation) {
  auto result = PreprocessAndGet(
      "`define V 8'd10\n"
      "`define V 8'd25\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `V;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 25u);
}

TEST(DefineSimulation, NestedMacroSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`define INNER 8'd4\n"
      "`define OUTER (`INNER + 8'd6)\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `OUTER;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 10u);
}

TEST(DefineSimulation, MacroWithDefaultArgSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`define ADD(a, b=8'd50) (a + b)\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `ADD(8'd3);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 53u);
}

// End-to-end over the string-literal dependency (5.9): a `" macro-quote builds
// a real string literal from the actual argument. Driven through the full
// pipeline, the resulting one-character string assigns its ASCII code to the
// byte-wide destination.
TEST(DefineSimulation, BacktickQuoteConstructedStringSimulates) {
  auto result = PreprocessAndGet(
      "`define CH(c) `\"c`\"\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `CH(A);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 0x41u);
}

// End-to-end over the escaped-identifier dependency (5.6.1): an escaped
// identifier used as the macro name defines and expands correctly through the
// full pipeline.
TEST(DefineSimulation, EscapedIdentifierMacroNameSimulates) {
  auto result = PreprocessAndGet(
      "`define \\M@X 8'd9\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `\\M@X ;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 9u);
}

// End-to-end over the comment dependency (5.4): a one-line comment in the macro
// body is stripped and does not become part of the substituted text, so the
// numeric body still elaborates and simulates.
TEST(DefineSimulation, MacroBodyCommentStrippedSimulates) {
  auto result = PreprocessAndGet(
      "`define V 8'd7 // trailing note\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `V;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 7u);
}
