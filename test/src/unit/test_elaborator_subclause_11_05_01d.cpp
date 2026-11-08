#include <gtest/gtest.h>

#include <optional>

#include "elaborator/const_eval.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_param_value.h"

using namespace delta;

namespace {

TEST(ConstantSelectFold, PartSelectOfSixtyFourBitsOrMoreFolds) {
  EvalFixture f;
  EXPECT_EQ(
      ConstEvalInt(ParseExprFrom("{8'h1, 64'hFFFF_FFFF_FFFF_FFFF}[63:0]", f)),
      -1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{8'h5A, 64'h0}[71:64]", f)), 0x5A);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{8'h5A, 64'h3}[71:0]", f)), 3);
}

TEST(ConstantSelectFold, SelectOutsideTheVectorDoesNotFold) {
  EvalFixture f;
  for (const char* text :
       {"{8'hFF}[9]", "{8'hFF}[-1]", "{8'hFF}[9:6]", "{8'hFF}[1:-2]"}) {
    EXPECT_EQ(ConstEvalInt(ParseExprFrom(text, f)), std::nullopt) << text;
  }
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{8'hA5}[3:0]", f)), 5);
}

TEST(ConstantSelectFold, ParameterSelectsFoldThroughTheDeclaredRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter logic [127:0] W = {64'h1, 64'hFFFF_FFFF_FFFF_FFFF};\n"
      "  localparam logic [63:0] L = W[63:0];\n"
      "  localparam logic [31:0] P = 32'h1234_5678;\n"
      "  localparam logic [7:0] Q = P[0 +: 8];\n"
      "  localparam logic [7:0] R = P[15 -: 8];\n"
      "  localparam logic [7:0] S = P[12 -: 8];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(ParamValue(design, "L"), -1);
  EXPECT_EQ(ParamValue(design, "Q"), 0x78);
  EXPECT_EQ(ParamValue(design, "R"), 0x56);
  EXPECT_EQ(ParamValue(design, "S"), 0xB3);
}

}  // namespace
