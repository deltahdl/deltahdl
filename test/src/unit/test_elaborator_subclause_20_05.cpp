#include <gtest/gtest.h>

#include <cstdint>

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

TEST(ConversionFunctions, BitPatternFunctionsFoldToTheirExactValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [63:0] A = $realtobits(0.1);\n"
      "  localparam logic [31:0] B = $shortrealtobits(0.1);\n"
      "  localparam real C = $bitstoreal(64'h3FB999999999999A);\n"
      "  localparam real D = $bitstoshortreal(32'h3DCCCCCD);\n"
      "  parameter bit [63:0] E = $realtobits(-2.0);\n"
      "  localparam longint F = $shortrealtobits(-1.0);\n"
      "  localparam G = $realtobits(0.1);\n"
      "  localparam real H = $itor(5) / 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto& params = design->top_modules[0]->params;
  ASSERT_EQ(params.size(), 8u);
  EXPECT_EQ(static_cast<uint64_t>(params[0].resolved_value),
            0x3FB999999999999Au);
  EXPECT_EQ(params[1].resolved_value, 0x3DCCCCCD);
  EXPECT_EQ(params[2].resolved_real, 0.1);
  EXPECT_EQ(params[3].resolved_real, static_cast<double>(0.1F));
  EXPECT_EQ(static_cast<uint64_t>(params[4].resolved_value),
            0xC000000000000000u);
  EXPECT_EQ(params[5].resolved_value, 0xBF800000);
  EXPECT_EQ(static_cast<uint64_t>(params[6].resolved_value),
            0x3FB999999999999Au);
  EXPECT_EQ(params[7].resolved_real, 2.5);
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
