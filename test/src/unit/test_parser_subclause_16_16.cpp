#include <gtest/gtest.h>

#include <string_view>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(ClockResolutionParse, ClockingBlockPropertyWithoutClockIsLegal) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    property p1;\n"
      "      $fell(c) |=> b;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClockResolutionParse, ClockingBlockPropertyWithExplicitClockIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    property p1;\n"
      "      @(posedge clk) a |=> b;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "a property declared in a clocking block may not "
                            "specify an explicit clocking event",
                            4, "16.16"));
}

TEST(ClockResolutionParse, ClockingBlockSequenceWithoutClockIsLegal) {
  auto r = Parse(
      "module m;\n"
      "  logic b, c, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence s1;\n"
      "      b ##1 c;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClockResolutionParse, ClockingBlockSequenceWithExplicitClockIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic b, c, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence s1;\n"
      "      @(posedge clk) b ##1 c;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "a sequence declared in a clocking block may not "
                            "specify an explicit clocking event",
                            4, "16.16"));
}

TEST(ClockResolutionParse,
     ExplicitClockLegalOnDeclarationOutsideClockingBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, clk;\n"
      "  property p1;\n"
      "    @(posedge clk) a |=> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClockResolutionParse, DefaultClockingBlockPropertyWithoutClockIsLegal) {
  auto r = Parse(
      "module m;\n"
      "  logic c, clk;\n"
      "  default clocking pc @(posedge clk);\n"
      "    property p3;\n"
      "      $fell(c) |=> c;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClockResolutionParse, ClockingBlockMulticlockedPropertyIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    property p1;\n"
      "      a |=> @(negedge clk) b;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "a multiclocked property is not allowed in a clocking block", 4,
      "16.16"));
}

TEST(ClockResolutionParse, ClockingBlockMulticlockedSequenceIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence s1;\n"
      "      a ##1 @(negedge clk) b;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "a multiclocked sequence is not allowed in a clocking block", 4,
      "16.16"));
}

TEST(ClockResolutionParse, ClockingBlockSequenceWithTwoClocksIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence s1;\n"
      "      @(posedge clk) a ##1 @(negedge clk) b;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "a multiclocked sequence is not allowed in a clocking block", 4,
      "16.16"));
}

const ModuleItem* NamedSequence(const ParseResult& r, std::string_view name) {
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl && item->name == name) {
      return item;
    }
  }
  return nullptr;
}

TEST(ClockResolutionParse, ASequenceKeepsItsLeadingClockOverANestedGroup) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, d, e, clk;\n"
      "  sequence s;\n"
      "    @(posedge clk) ((a ##5 b) and (c ##8 d)) ##0 e;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* s = NamedSequence(r, "s");
  ASSERT_NE(s, nullptr);
  ASSERT_EQ(s->seq_clock.size(), 1u);
  EXPECT_EQ(s->seq_clock[0].edge, Edge::kPosedge);
  ASSERT_NE(s->seq_clock[0].signal, nullptr);
  EXPECT_EQ(s->seq_clock[0].signal->text, "clk");
  ASSERT_EQ(s->seq_linear.operands.size(), 2u);
  const PropertyExprNode* group = s->seq_linear.operands[0]->property_actual;
  ASSERT_NE(group, nullptr);
  EXPECT_EQ(group->kind, PropertyExprNode::Kind::kSequence);
  ASSERT_NE(group->sequence, nullptr);
  EXPECT_EQ(group->sequence->seq_linear.conjuncts.size(), 1u);
}

TEST(ClockResolutionParse, ASequenceWithoutALeadingClockRecordsNone) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, d, e, clk;\n"
      "  sequence s;\n"
      "    ((a ##[1:6] b) and (c ##[1:9] d)) ##0 e;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* s = NamedSequence(r, "s");
  ASSERT_NE(s, nullptr);
  EXPECT_TRUE(s->seq_clock.empty());
  EXPECT_EQ(s->seq_linear.operands.size(), 2u);
}

TEST(ClockResolutionParse, ASequenceKeepsABareNamedLeadingClock) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  event e;\n"
      "  sequence s;\n"
      "    @e a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* s = NamedSequence(r, "s");
  ASSERT_NE(s, nullptr);
  ASSERT_EQ(s->seq_clock.size(), 1u);
  EXPECT_EQ(s->seq_clock[0].edge, Edge::kNone);
  ASSERT_NE(s->seq_clock[0].signal, nullptr);
  EXPECT_EQ(s->seq_clock[0].signal->text, "e");
  EXPECT_EQ(s->seq_linear.operands.size(), 2u);
}

TEST(ClockResolutionParse, ABareNamedLeadingClockEndsAtTheName) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  event e;\n"
      "  sequence s;\n"
      "    @e (a) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* s = NamedSequence(r, "s");
  ASSERT_NE(s, nullptr);
  ASSERT_EQ(s->seq_clock.size(), 1u);
  ASSERT_NE(s->seq_clock[0].signal, nullptr);
  EXPECT_EQ(s->seq_clock[0].signal->kind, ExprKind::kIdentifier);
  EXPECT_EQ(s->seq_clock[0].signal->text, "e");
  EXPECT_EQ(s->seq_linear.operands.size(), 2u);
}

}  // namespace
