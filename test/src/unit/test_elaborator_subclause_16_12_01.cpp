#include <gtest/gtest.h>

#include "elaborator/property_instantiation.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(PropertyInstantiation, LegalAsPropertyExprWhenBodyFits) {
  // §16.12.1: an instance is legal as a property_expr provided the named
  // property's body — with actuals substituted for formals — is itself a
  // legal property_expr.
  EXPECT_TRUE(
      IsPropertyInstanceLegal(PropertyInstancePlacement::kAsPropertyExpr,
                              /*body_substitutable_at_placement=*/true));
}

TEST(PropertyInstantiation, RejectedWhenSubstitutionWouldBeIllegal) {
  // §16.12.1: if substituting actuals would not yield a legal property at
  // the placement, the instance is not legal.
  EXPECT_FALSE(
      IsPropertyInstanceLegal(PropertyInstancePlacement::kAsPropertyExpr,
                              /*body_substitutable_at_placement=*/false));
}

// §16.12.1: an instance of a named property used as a property_expr operand of
// a property-building operator must yield a legal property_expr once its body
// is substituted. A disable iff clause turns the flattened body into a
// property_spec, which is not a legal operand — so a named property carrying a
// disable iff clause may not appear as such an operand. Here `leaf` has a
// disable iff clause and is instantiated as the operand of the `not` property
// operator inside `outer`, which is illegal. Note the flattened disable iff
// count of `outer` is only one, so this is NOT caught by §16.12's no-nesting
// rule — it is specifically the §16.12.1 operand restriction.
TEST(PropertyInstantiation, DisableIffPropertyRejectedAsOperandOfPropertyOp) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (rst) a |-> b;\n"
      "  endproperty\n"
      "  property outer;\n"
      "    @(posedge clk) not leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.12.1: the operand restriction is specifically about the disable iff
// clause. The same `not leaf()` operand position is legal when the instantiated
// property carries no disable iff clause, because its substituted body is a
// legal property_expr.
TEST(PropertyInstantiation, PropertyWithoutDisableIffAcceptedAsOperand) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property leaf;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  property outer;\n"
      "    @(posedge clk) not leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.12.1: a named property that carries a disable iff clause is still legal
// when its instance stands as the whole property_spec rather than as an operand
// of a property-building operator. Here `leaf` (with disable iff) is the sole
// body of `outer`, so it is the top-level property_spec, not an operand, and
// the instantiation is legal.
TEST(PropertyInstantiation, DisableIffPropertyAcceptedAsTopLevelInstance) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (rst) a |-> b;\n"
      "  endproperty\n"
      "  property outer;\n"
      "    leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.12.1: the operand restriction applies to every property-building
// operator, not only `not`. Here `leaf` (with disable iff) is the operand of
// the strong prefix operator `s_eventually`, a different syntactic position
// than the earlier `not` test, and the instantiation is still illegal.
TEST(PropertyInstantiation,
     DisableIffPropertyRejectedAsStrongEventuallyOperand) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (rst) a |-> b;\n"
      "  endproperty\n"
      "  property outer;\n"
      "    @(posedge clk) s_eventually leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.12.1: the operand restriction also covers the right operand of an infix
// property operator. Here `leaf` (with disable iff) is the right operand of
// `s_until`, so the instantiation is illegal.
TEST(PropertyInstantiation, DisableIffPropertyRejectedAsInfixUntilOperand) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (rst) a |-> b;\n"
      "  endproperty\n"
      "  property outer;\n"
      "    @(posedge clk) a s_until leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.12.1: the same infix right-operand position is legal when the
// instantiated property carries no disable iff clause, confirming the rule
// keys on the disable iff clause rather than on the operator position itself.
TEST(PropertyInstantiation,
     PropertyWithoutDisableIffAcceptedAsInfixUntilOperand) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property leaf;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  property outer;\n"
      "    @(posedge clk) a s_until leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.12.1 end to end with §F.4.1 flattening: a named property "has" a disable
// iff clause for this rule even when the clause is contributed by a property it
// instantiates rather than written directly. `leaf` carries no disable iff of
// its own but instantiates `mid`, which does; once flattened, `leaf` has a
// disable iff clause, so using it as the operand of `not` is illegal. The
// disable iff is produced through real nested property instantiation, not by
// hand-building the flattened state.
TEST(PropertyInstantiation,
     PropertyRejectedAsOperandWhenDisableIffFromFlattening) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property mid;\n"
      "    @(posedge clk) disable iff (rst) a |-> b;\n"
      "  endproperty\n"
      "  property leaf;\n"
      "    @(posedge clk) mid();\n"
      "  endproperty\n"
      "  property outer;\n"
      "    @(posedge clk) not leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
