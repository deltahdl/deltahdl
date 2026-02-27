// §11.4.11: Conditional operator

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstEval, Ternary) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 ? 42 : 99", f)), 42);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 ? 42 : 99", f)), 99);
}

TEST(ConstEval, ScopedTernary) {
  EvalFixture f;
  ScopeMap scope_big = {{"WIDTH", 16}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("WIDTH > 8 ? WIDTH : 8", f), scope_big),
            16);
  ScopeMap scope_small = {{"WIDTH", 4}};
  EXPECT_EQ(
      ConstEvalInt(ParseExprFrom("WIDTH > 8 ? WIDTH : 8", f), scope_small), 8);
}

// § conditional_expression — ternary in continuous assignment elaborates
TEST(ElabA83, TernaryInContAssignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic sel;\n"
      "  wire [7:0] a, b, y;\n"
      "  assign y = sel ? a : b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
