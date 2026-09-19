#include <gtest/gtest.h>

#include "elaborator/property_instantiation.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

// The process a static concurrent assertion is lowered to (§16.14.5 gives it
// always semantics, so it is a kAlwaysFF), or nullptr when the module holds
// none. The last three cases read the instance's substituted clock and body
// off it.
const RtlirProcess* AssertionProcess(const RtlirModule* mod) {
  for (const auto& p : mod->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysFF) return &p;
  }
  return nullptr;
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"leaf\" has a disable iff clause and "
                            "cannot be used as an operand of a property "
                            "operator in \"outer\"",
                            5, "16.12.1"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"leaf\" has a disable iff clause and "
                            "cannot be used as an operand of a property "
                            "operator in \"outer\"",
                            5, "16.12.1"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"leaf\" has a disable iff clause and "
                            "cannot be used as an operand of a property "
                            "operator in \"outer\"",
                            5, "16.12.1"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"leaf\" has a disable iff clause and "
                            "cannot be used as an operand of a property "
                            "operator in \"outer\"",
                            8, "16.12.1"));
}

// §16.12.1: an instance of a named property can be used as a property_spec,
// legal when the body substituted in place of the instance is a legal
// property_spec. The instance here is the whole spec of an assert property, and
// the body is the clocked boolean form, so the assertion is the process an
// assert property written as `@(posedge clk) !req || en` is: clocked by the
// property's leading event, carrying the property's boolean as a concurrent
// clocked body, and carrying the assertion's own action block. An
// implementation that left the instance unevaluated would build no process.
TEST(PropertyInstantiation, InstanceAsPropertySpecIsTheBodysProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, req, en;\n"
      "  int fails = 0;\n"
      "  property req_only_when_enabled;\n"
      "    @(posedge clk) !req || en;\n"
      "  endproperty\n"
      "  assert property (req_only_when_enabled) else fails = fails + 1;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  const RtlirProcess* p = AssertionProcess(design->top_modules[0]);
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_concurrent_clocked);
  ASSERT_EQ(p->sensitivity.size(), 1u);
  EXPECT_EQ(p->sensitivity[0].edge, Edge::kPosedge);
  ASSERT_NE(p->sensitivity[0].signal, nullptr);
  EXPECT_EQ(p->sensitivity[0].signal->text, "clk");
  ASSERT_NE(p->body, nullptr);
  EXPECT_EQ(p->body->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(p->body->is_concurrent_clocked);
  ASSERT_NE(p->body->assert_expr, nullptr);
  EXPECT_EQ(p->body->assert_expr->kind, ExprKind::kBinary);
  EXPECT_EQ(p->body->assert_pass_stmt, nullptr);
  EXPECT_NE(p->body->assert_fail_stmt, nullptr);
}

// A spec that is one name is an instance only when the name is a property's.
// Here it is a variable's, so the spec is the boolean the name reads as,
// and §16.16 (f) makes an assertion with no leading clocking event, no
// default clocking in scope and no instance to determine one illegal; the
// parser left it to the elaborator, which has the default clocking, to say.
TEST(PropertyInstantiation, ANameThatIsNoPropertysIsABooleanWithoutAClock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  assert property (a);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assertion has no leading clocking "
                            "event",
                            3, "16.16"));
  EXPECT_EQ(AssertionProcess(design->top_modules[0]), nullptr);
}

// The substitution reaches a body in the clocked boolean form and, since
// §16.12.17 was evaluated, a body the tree evaluator reads: one holding an
// implication is such a body, so the instance is the process the assertion
// written with that spec is, its tree rooted at the instance for the
// evaluator to expand.
TEST(PropertyInstantiation, AnInstanceOfATemporalPropertyIsTheBodysProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  property p_base;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  assert property (p_base);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirProcess* p = AssertionProcess(design->top_modules[0]);
  ASSERT_NE(p, nullptr);
  ASSERT_EQ(p->sensitivity.size(), 1u);
  EXPECT_EQ(p->sensitivity[0].signal->text, "clk");
  ASSERT_NE(p->body, nullptr);
  ASSERT_NE(p->body->assert_property, nullptr);
  EXPECT_EQ(p->body->assert_property->kind, PropertyExprNode::Kind::kBoolean);
  ASSERT_NE(p->body->assert_property->boolean, nullptr);
  EXPECT_EQ(p->body->assert_property->boolean->text, "p_base");
}

// A body with no leading clocking event leaves an instance that is the
// whole spec with no clock to evaluate on: §16.16 (a) would take the default
// clocking, and with none in scope §16.16 (f) makes the assertion illegal,
// so it is reported and no process is built.
TEST(PropertyInstantiation, AnInstanceOfAnUnclockedPropertyIsReported) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  property p_base;\n"
      "    a |-> b;\n"
      "  endproperty\n"
      "  assert property (p_base);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assertion has no leading clocking "
                            "event",
                            6, "16.16"));
  EXPECT_EQ(AssertionProcess(design->top_modules[0]), nullptr);
}

}  // namespace
