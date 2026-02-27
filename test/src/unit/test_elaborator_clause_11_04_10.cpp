// §11.4.10: Shift operators

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstEval, Shifts) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 << 4", f)), 16);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("16 >> 2", f)), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 <<< 4", f)), 16);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("16 >>> 2", f)), 4);
}

// § binary_operator — shift operators elaborate
TEST(ElabA86, BinaryArithShiftRightElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd128 >>> 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA86, BinaryArithShiftLeftElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd1 <<< 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
