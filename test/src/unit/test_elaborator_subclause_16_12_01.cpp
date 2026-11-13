#include <gtest/gtest.h>

#include <cstdint>
#include <string>

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

constexpr const char* kDisableIffOperandReport =
    "has a disable iff clause and cannot be used as an operand of a property "
    "operator";

constexpr const char* kLeafWithDisableIff =
    "  property leaf; disable iff (rst) a |-> b; endproperty\n";
constexpr const char* kLeafWithoutDisableIff =
    "  property leaf; a |-> b; endproperty\n";

const char* const kOperandUses[] = {
    "not leaf",
    "leaf or b",
    "b or leaf",
    "leaf implies b",
    "b implies leaf",
    "leaf iff b",
    "a |-> leaf",
    "a |=> leaf",
    "a #-# leaf",
    "a #=# leaf",
    "if (a) leaf",
    "if (a) b else leaf",
    "case (a) 1'b1: leaf; default: b; endcase",
    "leaf until b",
    "b until leaf",
    "leaf until_with b",
    "leaf s_until_with b",
    "always leaf",
    "always [1:2] leaf",
    "s_always [1:2] leaf",
    "eventually [1:2] leaf",
    "s_eventually [1:2] leaf",
    "nexttime leaf",
    "nexttime [2] leaf",
    "s_nexttime leaf",
    "accept_on (a) leaf",
    "reject_on (a) leaf",
    "sync_accept_on (a) leaf",
    "sync_reject_on (a) leaf",
};

std::string OperandModule(const std::string& leaf, const std::string& use) {
  return "module m;\n"
         "  logic clk;\n"
         "  bit a, b, rst;\n" +
         leaf + "  property outer; @(posedge clk) " + use +
         "; endproperty\n"
         "endmodule\n";
}

void ExpectDisableIffOperandReported(const std::string& src,
                                     const std::string& marker) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  uint32_t line = LineHolding(src, marker);
  ASSERT_NE(line, 0u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kDisableIffOperandReport,
                            line, "16.12.1"));
}

void ExpectInstanceAccepted(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PropertyInstanceOperand, ADisableIffInstanceUnderEachOperatorIsReported) {
  for (const char* use : kOperandUses) {
    ExpectDisableIffOperandReported(OperandModule(kLeafWithDisableIff, use),
                                    "property outer;");
  }
}

TEST(PropertyInstanceOperand,
     AnInstanceWithoutDisableIffUnderEachOperatorIsAccepted) {
  for (const char* use : kOperandUses) {
    ExpectInstanceAccepted(OperandModule(kLeafWithoutDisableIff, use));
  }
}

TEST(PropertyInstanceOperand,
     DISABLED_ADisableIffInstanceInParenthesesIsReported) {
  ExpectDisableIffOperandReported(OperandModule(kLeafWithDisableIff, "(leaf)"),
                                  "property outer;");
}

TEST(PropertyInstanceOperand, ADisableIffInstanceUnderALeadingClockIsAccepted) {
  ExpectInstanceAccepted(OperandModule(kLeafWithDisableIff, "leaf"));
  ExpectInstanceAccepted(
      "module m;\n"
      "  logic clk;\n"
      "  bit a, b, rst;\n" +
      std::string(kLeafWithDisableIff) +
      "  a1: assert property (@(posedge clk) leaf);\n"
      "  always @(posedge clk) a2: assert property (leaf);\n"
      "endmodule\n");
}

TEST(PropertyInstanceOperand, ADisableIffInstanceWithArgumentsIsReported) {
  ExpectDisableIffOperandReported(
      "module m;\n"
      "  logic clk;\n"
      "  bit a, b, rst;\n"
      "  property leaf(x, y); disable iff (rst) x |-> y; endproperty\n"
      "  property outer; @(posedge clk) a |-> leaf(a, b); endproperty\n"
      "endmodule\n",
      "property outer;");
}

std::string OperandIn(const std::string& place, const std::string& leaf,
                      const std::string& use) {
  std::string decl =
      leaf + "  property outer; @(posedge clk) " + use + "; endproperty\n";
  if (place == "assertion") {
    return "module m;\n  logic clk;\n  bit a, b, rst;\n" + leaf +
           "  a1: assert property (@(posedge clk) " + use + ");\nendmodule\n";
  }
  if (place == "procedural") {
    return "module m;\n  logic clk;\n  bit a, b, rst;\n" + leaf +
           "  always @(posedge clk) a1: assert property (" + use +
           ");\nendmodule\n";
  }
  if (place == "interface" || place == "program") {
    return place + " el(input logic clk, a, b, rst);\n" + decl + "end" + place +
           "\nmodule m; logic clk, a, b, rst; el u(clk, a, b, rst); "
           "endmodule\n";
  }
  if (place == "checker") {
    return "checker el(logic clk, logic a, logic b, logic rst);\n" + decl +
           "endchecker\nmodule m; logic clk, a, b, rst; el u(clk, a, b, rst);"
           " endmodule\n";
  }
  if (place == "package") {
    return "package pk;\n  bit clk, a, b, rst;\n" + decl +
           "endpackage\nmodule m; endmodule\n";
  }
  if (place == "unit") {
    return "bit clk, a, b, rst;\n" + decl + "module m; endmodule\n";
  }
  if (place == "package instance") {
    return "package pk;\n  bit a, b, rst;\n" + leaf +
           "endpackage\nmodule m;\n  logic clk;\n  bit a, b;\n"
           "  property outer; @(posedge clk) " +
           std::string(use).replace(std::string(use).find("leaf"), 4,
                                    "pk::leaf") +
           "; endproperty\nendmodule\n";
  }
  return "module m;\n  logic clk;\n  bit a, b, rst;\n  if (1) begin : g\n" +
         decl + "  end\nendmodule\n";
}

const char* const kCheckedOperandPlaces[] = {"assertion",        "interface",
                                             "program",          "checker",
                                             "package instance", "generate"};
const char* const kUncheckedOperandPlaces[] = {"procedural", "package", "unit"};

TEST(PropertyInstanceOperand,
     ADisableIffInstanceAsAnOperandInEachPlaceIsReported) {
  for (const char* place : kCheckedOperandPlaces) {
    SCOPED_TRACE(place);
    std::string src = OperandIn(place, kLeafWithDisableIff, "a |-> leaf");
    ExpectDisableIffOperandReported(
        src,
        std::string(place) == "package instance" ? "|-> pk::leaf" : "|-> leaf");
  }
}

TEST(PropertyInstanceOperand,
     DISABLED_ADisableIffInstanceAsAnOperandOutsideTheCheckedPlacesIsReported) {
  for (const char* place : kUncheckedOperandPlaces) {
    SCOPED_TRACE(place);
    std::string src = OperandIn(place, kLeafWithDisableIff, "a |-> leaf");
    ExpectDisableIffOperandReported(
        src,
        std::string(place) == "package instance" ? "|-> pk::leaf" : "|-> leaf");
  }
}

TEST(PropertyInstanceOperand,
     AnInstanceWithoutDisableIffInEachPlaceIsAccepted) {
  for (const char* place : kCheckedOperandPlaces) {
    SCOPED_TRACE(place);
    ExpectInstanceAccepted(
        OperandIn(place, kLeafWithoutDisableIff, "a |-> leaf"));
  }
  for (const char* place : kUncheckedOperandPlaces) {
    SCOPED_TRACE(place);
    ExpectInstanceAccepted(
        OperandIn(place, kLeafWithoutDisableIff, "a |-> leaf"));
  }
}

}  // namespace
