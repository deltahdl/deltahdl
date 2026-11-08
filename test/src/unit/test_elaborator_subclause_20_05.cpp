#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

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

TEST(ConversionFunctions, RtoiFoldsToA32BitInteger) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam longint A = $rtoi(3.0e9);\n"
      "  localparam longint B = $rtoi(-3.0e9);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->params[0].resolved_value, -1294967296);
  EXPECT_EQ(design->top_modules[0]->params[1].resolved_value, 1294967296);
}

}  // namespace
