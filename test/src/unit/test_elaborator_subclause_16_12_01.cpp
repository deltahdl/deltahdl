#include <gtest/gtest.h>

#include "elaborator/property_instantiation.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

const RtlirProcess* AssertionProcess(const RtlirModule* mod) {
  for (const auto& p : mod->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysFF) return &p;
  }
  return nullptr;
}

TEST(PropertyInstantiation, LegalAsPropertyExprWhenBodyFits) {
  EXPECT_TRUE(IsPropertyInstanceLegal(
      PropertyInstancePlacement::kAsPropertyExpr, true));
}

TEST(PropertyInstantiation, RejectedWhenSubstitutionWouldBeIllegal) {
  EXPECT_FALSE(IsPropertyInstanceLegal(
      PropertyInstancePlacement::kAsPropertyExpr, false));
}

TEST(PropertyInstantiation, DisableIffPropertyRejectedAsOperandOfPropertyOp) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, rst, a, b);\n"
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

TEST(PropertyInstantiation, PropertyWithoutDisableIffAcceptedAsOperand) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, a, b);\n"
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

TEST(PropertyInstantiation, DisableIffPropertyAcceptedAsTopLevelInstance) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, rst, a, b);\n"
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

TEST(PropertyInstantiation,
     DisableIffPropertyRejectedAsStrongEventuallyOperand) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, rst, a, b);\n"
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

TEST(PropertyInstantiation, DisableIffPropertyRejectedAsInfixUntilOperand) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, rst, a, b);\n"
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

TEST(PropertyInstantiation,
     PropertyWithoutDisableIffAcceptedAsInfixUntilOperand) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, a, b);\n"
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

TEST(PropertyInstantiation,
     PropertyRejectedAsOperandWhenDisableIffFromFlattening) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, rst, a, b);\n"
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

TEST(PropertyInstantiation, DisableIffPropertyRejectedAsAndOperandInAssertion) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic clk;\n"
      "  bit a, b, rst;\n"
      "  property p1; disable iff (rst) a |=> b; endproperty\n"
      "  assert property (@(posedge clk) p1 and b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"p1\" has a disable iff clause and "
                            "cannot be used as an operand of a property "
                            "operator",
                            5, "16.12.1"));
}

TEST(PropertyInstantiation, DisableIffPropertyRejectedAsAndOperandInDecl) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic clk;\n"
      "  bit a, b, rst;\n"
      "  property leaf; disable iff (rst) a |=> b; endproperty\n"
      "  property outer;\n"
      "    @(posedge clk) leaf and b;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"leaf\" has a disable iff clause and "
                            "cannot be used as an operand of a property "
                            "operator in \"outer\"",
                            5, "16.12.1"));
}

TEST(PropertyInstantiation, DisableIffPropertyAcceptedAsWholeAssertionSpec) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk;\n"
      "  bit a, b, rst;\n"
      "  property p1; @(posedge clk) disable iff (rst) a |=> b; endproperty\n"
      "  assert property (p1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
