#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

// §11.3.3 governs how an integer literal is interpreted (signed vs unsigned)
// when it is used as an operand of an expression. The distinguishing vehicle
// the LRM itself uses is "minus twelve divided by three": negation followed by
// division, where the sign attribute of the literal decides whether the
// division is signed (result -4) or unsigned (a large positive value). Every
// test below builds the literal from real source syntax (the literal is the
// default value of a module parameter, parsed by the production parser) and
// folds it through the elaborator's constant evaluator, so the signedness rule
// is observed exactly as production applies it -- not by hand-constructing a
// literal node and stamping a sign flag on it.

// SHALL #2: a literal with no base specifier is a signed, two's-complement
// value, so -12 / 3 divides as signed and yields -4.
TEST(IntegerLiteralElaboration, NegatedUnbasedDivThreeEqualsMinusFour) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), -4);
}

// SHALL #3: an unsized literal with an unsigned base specifier ('d) is
// unsigned, so -'d12 negates and divides as an unsigned 32-bit quantity and
// yields 1431655761 rather than -4. This is the crux of SHALL #1: the negative
// with a base specifier is interpreted differently from the negative without.
TEST(IntegerLiteralElaboration, NegatedUnsignedBasedDivThree) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-'d12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), 1431655761);
}

// A signed base specifier ('sd) restores signed interpretation, so -'sd12 / 3
// again yields -4, matching the unbased form and contrasting with 'd.
TEST(IntegerLiteralElaboration, NegatedSignedBasedDivThreeEqualsMinusFour) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-'sd12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), -4);
}

// A sized signed-based literal: -4'sd12 is the negation of the 4-bit signed
// quantity 1100 (= -4), so -(-4) = 4 and 4 / 3 = 1.
TEST(IntegerLiteralElaboration, NegatedSizedSignedBasedDivThreeEqualsOne) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-4'sd12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), 1);
}

// SHALL #3 for the *sized* unsigned-based form (the third enumerated literal
// form, "a sized, based integer"): a sized unsigned base specifier is unsigned
// exactly like the unsized form. -32'd12 negates and divides as an unsigned
// 32-bit value, so the result equals the unsized -'d12 / 3 result 1431655761,
// confirming the sign rule is driven by the base specifier and not by whether
// the literal carries a size.
TEST(IntegerLiteralElaboration, NegatedSizedUnsignedBasedDivThree) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-32'd12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), 1431655761);
}

// The two tests below drive the sign rule through a *parameter* and a
// *localparam* initializer, elaborated end to end: the literal is written in
// its real source form (§5.7.1 syntax), the elaborator folds the whole
// initializer at elaboration time, and the resolved parameter value is read
// back from the design. This exercises the parameter/localparam constant-form
// code path, distinct from folding a plucked sub-expression, and observes the
// SHALL #1 contrast (unsigned-based vs unbased) at that path.

// SHALL #3 via a parameter: the unsigned-based literal makes the negation and
// division unsigned, so the parameter resolves to 1431655761, not -4.
TEST(IntegerLiteralElaboration, ParameterUnsignedBasedLiteralResolvesUnsigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = -'d12 / 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 1431655761);
}

// SHALL #2 via a localparam: the unbased literal is signed, so the same
// negation and division resolve to -4.
TEST(IntegerLiteralElaboration, LocalparamUnbasedLiteralResolvesSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int Q = -12 / 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& q = design->top_modules[0]->params[0];
  EXPECT_EQ(q.name, "Q");
  EXPECT_TRUE(q.is_resolved);
  EXPECT_EQ(q.resolved_value, -4);
}

}  // namespace
