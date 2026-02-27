// §20.6.2: Expression size system function

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstEval, BitsExpr) {
  EvalFixture f;
  // §20.6.2: $bits(8'hFF) should return 8 (width of expression).
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(8'hFF)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(16'h0)", f)), 16);
}

// § system_tf_call — $bits with expression argument
TEST(ElabA82, SystemTfCallBitsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  logic [31:0] x;\n"
      "  initial x = $bits(v);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
