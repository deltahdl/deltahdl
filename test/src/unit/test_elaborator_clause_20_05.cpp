#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §20.5: the conversion functions may be used in constant expressions. These
// tests drive the six real/bit conversion functions through parameter
// initializers so the elaborator must fold them at elaboration time; the folded
// value is read back from the resolved parameter.

// $rtoi folds and truncates toward zero (it does not round): 3.9 -> 3, not 4.
TEST(ConversionFunctions, RtoiFoldsAndTruncatesInConstantContext) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int A = $rtoi(3.2);\n"
      "  parameter int B = $rtoi(3.9);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->params[0].name, "A");
  EXPECT_EQ(design->top_modules[0]->params[0].resolved_value, 3);
  EXPECT_EQ(design->top_modules[0]->params[1].name, "B");
  EXPECT_EQ(design->top_modules[0]->params[1].resolved_value, 3);
}

// $itor converts an integer to a real in a constant real context; here the
// folded real 5.0 + 0.5 = 5.5 is truncated back by $rtoi to 5.
TEST(ConversionFunctions, ItorFoldsInConstantContext) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int C = $rtoi($itor(5) + 0.5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->params[0].name, "C");
  EXPECT_EQ(design->top_modules[0]->params[0].resolved_value, 5);
}

// $realtobits / $bitstoreal round-trip a double through its 64-bit IEEE-754
// pattern in a constant context; the recovered 7.9 truncates to 7.
TEST(ConversionFunctions, RealtobitsBitstorealRoundTripInConstantContext) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int D = $rtoi($bitstoreal($realtobits(7.9)));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->params[0].name, "D");
  EXPECT_EQ(design->top_modules[0]->params[0].resolved_value, 7);
}

// $shortrealtobits / $bitstoshortreal round-trip a value through its 32-bit
// single-precision pattern in a constant context; 2.5 is exact, so it recovers
// to 2.5 and truncates to 2.
TEST(ConversionFunctions, ShortrealConversionRoundTripInConstantContext) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int E = $rtoi($bitstoshortreal($shortrealtobits(2.5)));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->params[0].name, "E");
  EXPECT_EQ(design->top_modules[0]->params[0].resolved_value, 2);
}

// §20.5 constant-expression input form: a localparam target folds the same way
// a parameter does. This is a distinct declaration path from the value
// parameter above.
TEST(ConversionFunctions, RtoiFoldsInLocalparamTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int A = $rtoi(6.7);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->params[0].name, "A");
  EXPECT_EQ(design->top_modules[0]->params[0].resolved_value, 6);
}

// §20.5 constant-expression input form: the argument is a parameter reference
// rather than a literal, so the fold resolves the operand through the constant
// scope. $itor consumes the value parameter P (7) -> 7.0; -0.5 -> 6.5; $rtoi
// truncates to 6.
TEST(ConversionFunctions, ConversionFoldsWithParameterArgument) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = 7;\n"
      "  localparam int B = $rtoi($itor(P) - 0.5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->params[1].name, "B");
  EXPECT_EQ(design->top_modules[0]->params[1].resolved_value, 6);
}

// §20.5 constant-expression input form: the argument is a localparam reference.
// $itor consumes localparam N (5) -> 5.0; +0.5 -> 5.5; $rtoi truncates to 5.
TEST(ConversionFunctions, ConversionFoldsWithLocalparamArgument) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int N = 5;\n"
      "  localparam int C = $rtoi($itor(N) + 0.5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->params[1].name, "C");
  EXPECT_EQ(design->top_modules[0]->params[1].resolved_value, 5);
}

}  // namespace
