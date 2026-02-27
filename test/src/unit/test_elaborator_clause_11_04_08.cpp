// §11.4.8: Bitwise operators

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstEval, Bitwise) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("12 & 10", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("12 | 3", f)), 15);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("5 ^ 3", f)), 6);
}

// § expression — unary operator in initial elaborates
TEST(ElabA83, UnaryExprInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = ~a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA86, UnaryBitwiseNotElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, a;\n"
      "  initial x = ~a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § binary_operator — bitwise operators elaborate
TEST(ElabA86, BinaryBitwiseXnorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hFF ^~ 8'h0F;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
