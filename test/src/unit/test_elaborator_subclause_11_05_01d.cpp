// §11.5.1 Vector bit-select and part-select addressing, folded as constant
// expressions: a part-select of any width, the indexed forms, and a select
// that reaches outside its vector, which a folded constant cannot answer
// because it holds no x (the run-time read is in
// test/src/unit/test_simulator_subclause_11_05_01e.cpp).

#include <gtest/gtest.h>

#include <optional>

#include "elaborator/const_eval.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_param_value.h"

using namespace delta;

namespace {

// A part-select of 64 bits or more folds from every word of its vector.
TEST(ConstantSelectFold, PartSelectOfSixtyFourBitsOrMoreFolds) {
  EvalFixture f;
  EXPECT_EQ(
      ConstEvalInt(ParseExprFrom("{8'h1, 64'hFFFF_FFFF_FFFF_FFFF}[63:0]", f)),
      -1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{8'h5A, 64'h0}[71:64]", f)), 0x5A);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{8'h5A, 64'h3}[71:0]", f)), 3);
}

// §11.5.1 has an out-of-bounds address read as x for a 4-state vector, which a
// folded constant does not hold, so such a select folds to nothing.
TEST(ConstantSelectFold, SelectOutsideTheVectorDoesNotFold) {
  EvalFixture f;
  for (const char* text :
       {"{8'hFF}[9]", "{8'hFF}[-1]", "{8'hFF}[9:6]", "{8'hFF}[1:-2]"}) {
    EXPECT_EQ(ConstEvalInt(ParseExprFrom(text, f)), std::nullopt) << text;
  }
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{8'hA5}[3:0]", f)), 5);
}

// A parameter takes the folded part-select of a 128-bit parameter's low 64
// bits, and the indexed forms select `width` bits up or down from their base.
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
