#include "helpers_preprocess_and_get.h"

TEST(UndefSimulation, UndefThenRedefineSimulatesNewValue) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd10\n"
      "`undef VAL\n"
      "`define VAL 8'd77\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 77u);
}

TEST(UndefSimulation, UndefExcludesConditionalCodeFromSimulation) {
  auto result = PreprocessAndGet(
      "`define USE_ALT\n"
      "`undef USE_ALT\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef USE_ALT\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = 8'd11;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 11u);
}

// Syntax 22-4 requires a separate text_macro_identifier after the keyword, so
// a line-leading `undefVAL is a usage of the macro undefVAL rather than an
// `undef of VAL. Both halves of that reading are observable in the simulated
// design: the macro body has to reach the module (there is no other source of
// an initial block) and VAL has to still be defined for the body to expand.
TEST(UndefSimulation, KeywordRunTogetherWithNameSimulatesAsMacroUsage) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd21\n"
      "`define undefVAL initial result = `VAL;\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`undefVAL\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 21u);
}

// Once the macro is removed it has no value at all, so redefining it as an
// object-like macro cannot inherit the formal argument list of the definition
// that `undef discarded.
TEST(UndefSimulation, RedefineAfterUndefDropsFormalArgumentsInSimulation) {
  auto result = PreprocessAndGet(
      "`define M(a,b) ((a)+(b))\n"
      "`undef M\n"
      "`define M 8'd54\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `M;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 54u);
}

// End-to-end over the §22.5.1 escaped-identifier macro name. That name form
// takes its own branch when the directive's operand is scanned, so driving it
// from real `define syntax all the way to a simulated value is the only way to
// see the removal actually reach the design.
TEST(UndefSimulation, UndefRemovesEscapedIdentifierMacroInSimulation) {
  auto result = PreprocessAndGet(
      "`define \\M@CRO 1\n"
      "`undef \\M@CRO\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef \\M@CRO\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = 8'd12;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 12u);
}

// End-to-end over the §22.5.1 macro that carries argument defaults. The branch
// taken is read straight from whether the macro is still defined, so nothing
// else in the source can account for the result: had the removal not happened,
// the other arm would have been compiled instead.
TEST(UndefSimulation, UndefRemovesMacroWithArgumentDefaultsInSimulation) {
  auto result = PreprocessAndGet(
      "`define OPT(a=8'd7,b=8'd9) (a)\n"
      "`undef OPT\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef OPT\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = 8'd31;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 31u);
}

TEST(UndefSimulation, UndefDoesNotAffectOtherMacroSimulation) {
  auto result = PreprocessAndGet(
      "`define A 8'd5\n"
      "`define B 8'd30\n"
      "`undef A\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `B;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 30u);
}
