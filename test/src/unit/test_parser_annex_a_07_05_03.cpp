#include <gtest/gtest.h>

#include <utility>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

TEST(TimingCheckEventDefParsing, ControlledTimingCheckEventPeriod) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(posedge clk, 50);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
}

TEST(TimingCheckEventDefParsing, TerminalPartSelect) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data[3:0], posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_terminal.name, "data");
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_NE(tc->data_terminal.range_left, nullptr);
  EXPECT_NE(tc->data_terminal.range_right, nullptr);
}

TEST(TimingCheckEventDefParsing, TimingCheckEventNoEdge) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kNone);
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNone);
  EXPECT_EQ(tc->data_terminal.name, "data");
  EXPECT_EQ(tc->ref_terminal.name, "clk");
}

TEST(TimingCheckEventDefParsing, BothEventsWithEdges) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setup(negedge d, posedge clk, 8);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "d");
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
}

TEST(TimingCheckEventDefParsing, TerminalSimpleIdentifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_terminal.name, "data");
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kNone);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
  EXPECT_EQ(tc->ref_terminal.range_kind, SpecifyRangeKind::kNone);
}

TEST(TimingCheckEventDefParsing, TimingCheckEventControlBareEdge) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kEdge);
  EXPECT_TRUE(tc->ref_edge_descriptors.empty());
}

TEST(TimingCheckEventDefParsing, EdgeControlSpecifierZeroOneDescriptors) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge[01, 10] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kEdge);
  ASSERT_EQ(tc->ref_edge_descriptors.size(), 2u);
  EXPECT_EQ(tc->ref_edge_descriptors[0], std::make_pair('0', '1'));
  EXPECT_EQ(tc->ref_edge_descriptors[1], std::make_pair('1', '0'));
}

TEST(TimingCheckEventDefParsing, EdgeDescriptorZorXThenZeroOrOne) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge[z0, x1, Z1, X0] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kEdge);
  ASSERT_EQ(tc->ref_edge_descriptors.size(), 4u);
  EXPECT_EQ(tc->ref_edge_descriptors[0], std::make_pair('z', '0'));
  EXPECT_EQ(tc->ref_edge_descriptors[1], std::make_pair('x', '1'));
  EXPECT_EQ(tc->ref_edge_descriptors[2], std::make_pair('Z', '1'));
  EXPECT_EQ(tc->ref_edge_descriptors[3], std::make_pair('X', '0'));
}

TEST(TimingCheckEventDefParsing, EdgeDescriptorZeroOrOneThenZorX) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge[0x, 1z, 0z, 1x] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kEdge);
  ASSERT_EQ(tc->ref_edge_descriptors.size(), 4u);
  EXPECT_EQ(tc->ref_edge_descriptors[0], std::make_pair('0', 'x'));
  EXPECT_EQ(tc->ref_edge_descriptors[1], std::make_pair('1', 'z'));
  EXPECT_EQ(tc->ref_edge_descriptors[2], std::make_pair('0', 'z'));
  EXPECT_EQ(tc->ref_edge_descriptors[3], std::make_pair('1', 'x'));
}

TEST(TimingCheckEventDefParsing, TimingCheckConditionBareExpression) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& en, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_NE(tc->data_condition, nullptr);
}

TEST(TimingCheckEventDefParsing, TimingCheckConditionParenthesized) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(negedge clk, data &&& (en), 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_NE(tc->data_condition, nullptr);
}

TEST(TimingCheckEventDefParsing, ScalarConditionNegation) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& ~en, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_NE(tc->data_condition, nullptr);
  EXPECT_EQ(tc->data_condition->kind, ExprKind::kUnary);
  EXPECT_EQ(tc->data_condition->op, TokenKind::kTilde);
}

TEST(TimingCheckEventDefParsing, ScalarConditionEqualityScalarConstant) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& en == 1'b1, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_NE(tc->data_condition, nullptr);
  EXPECT_EQ(tc->data_condition->kind, ExprKind::kBinary);
  EXPECT_EQ(tc->data_condition->op, TokenKind::kEqEq);
  EXPECT_NE(tc->data_condition->rhs, nullptr);
}

TEST(TimingCheckEventDefParsing, ScalarConditionCaseEqualityScalarConstant) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& en === 1'b0, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_NE(tc->data_condition, nullptr);
  EXPECT_EQ(tc->data_condition->kind, ExprKind::kBinary);
  EXPECT_EQ(tc->data_condition->op, TokenKind::kEqEqEq);
}

TEST(TimingCheckEventDefParsing, ScalarConditionInequalityScalarConstant) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& en != 'b1, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_NE(tc->data_condition, nullptr);
  EXPECT_EQ(tc->data_condition->kind, ExprKind::kBinary);
  EXPECT_EQ(tc->data_condition->op, TokenKind::kBangEq);
}

TEST(TimingCheckEventDefParsing, ScalarConditionCaseInequalityScalarConstant) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& en !== 1, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_NE(tc->data_condition, nullptr);
  EXPECT_EQ(tc->data_condition->kind, ExprKind::kBinary);
  EXPECT_EQ(tc->data_condition->op, TokenKind::kBangEqEq);
}

TEST(TimingCheckEventDefParsing, EscapedTerminalIdentifiers) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(\\data-in , posedge \\clk-1 , 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_terminal.name, "data-in");
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk-1");
}

TEST(TimingCheckEventDefParsing, EscapedInterfacePortTerminal) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(negedge \\bus-1 .\\rd-en , 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(tc->ref_terminal.interface_name, "bus-1");
  EXPECT_EQ(tc->ref_terminal.name, "rd-en");
}

TEST(TimingCheckEventDefParsing, EdgeDescriptorInvalidRejected) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge[01, 00] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "invalid edge_descriptor", 3, "31.5"));
}

TEST(TimingCheckEventDefParsing, EdgeControlSpecifierEmptyListRejected) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge[] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "edge-control specifier requires at least one edge_descriptor",
      3, "31.5"));
}

}  // namespace
