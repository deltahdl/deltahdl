#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

// §5.7.2: the default type of a fixed-point real literal is `real`, an IEEE 754
// double-precision (64-bit) value, rather than the 32-bit `shortreal`. The
// elaborator's width inference therefore reports 64 bits for such a literal.
TEST(RealLiteralElaboration, FixedPointDefaultsToRealWidth) {
  EvalFixture f;
  auto* e = ParseExprFrom("1.2", f);
  ASSERT_NE(e, nullptr);
  EXPECT_EQ(e->kind, ExprKind::kRealLiteral);
  EXPECT_EQ(InferExprWidth(e, {}), 64u);
}

// §5.7.2: the exponent (scientific) form likewise defaults to `real`, not the
// 32-bit `shortreal`.
TEST(RealLiteralElaboration, ExponentFormDefaultsToRealWidth) {
  EvalFixture f;
  auto* e = ParseExprFrom("2.0e10", f);
  ASSERT_NE(e, nullptr);
  EXPECT_EQ(e->kind, ExprKind::kRealLiteral);
  uint32_t w = InferExprWidth(e, {});
  EXPECT_EQ(w, 64u);
  EXPECT_NE(w, 32u);
}

TEST(RealLiteralElaboration, FixedPointElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  real x;\n"
      "  initial x = 2.718;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealLiteralElaboration, ScientificNotationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  real x;\n"
      "  initial x = 1.5e+3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealLiteralElaboration, ModuleWithRealLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  real r = 3.14;\n"
             "endmodule\n"));
}

TEST(RealLiteralElaboration, UnderscoreRealElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  real r = 236.123_763_e-12;\n"
             "endmodule\n"));
}

}  // namespace
