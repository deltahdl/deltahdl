#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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
  EXPECT_EQ(tc->ref_terminal.name, "data");
  EXPECT_EQ(tc->ref_terminal.range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_NE(tc->ref_terminal.range_left, nullptr);
  EXPECT_NE(tc->ref_terminal.range_right, nullptr);
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
  EXPECT_EQ(tc->ref_terminal.name, "data");
  EXPECT_EQ(tc->data_terminal.name, "clk");
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
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "d");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk");
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
  EXPECT_EQ(tc->ref_terminal.name, "data");
  EXPECT_EQ(tc->ref_terminal.range_kind, SpecifyRangeKind::kNone);
  EXPECT_EQ(tc->data_terminal.name, "clk");
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kNone);
}

// timing_check_event_control ::= ... | edge  -- bare 'edge' with no
// edge_control_specifier descriptor list.
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
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kEdge);
  EXPECT_TRUE(tc->data_edge_descriptors.empty());
}

// edge_control_specifier ::= edge [ edge_descriptor { , edge_descriptor } ]
// edge_descriptor ::= 01 | 10 ; covers the two zero_or_one zero_or_one forms.
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
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kEdge);
  ASSERT_EQ(tc->data_edge_descriptors.size(), 2u);
  EXPECT_EQ(tc->data_edge_descriptors[0], std::make_pair('0', '1'));
  EXPECT_EQ(tc->data_edge_descriptors[1], std::make_pair('1', '0'));
}

// edge_descriptor ::= z_or_x zero_or_one ; z_or_x ::= x|X|z|Z, zero_or_one ::= 0|1.
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
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kEdge);
  ASSERT_EQ(tc->data_edge_descriptors.size(), 4u);
  EXPECT_EQ(tc->data_edge_descriptors[0], std::make_pair('z', '0'));
  EXPECT_EQ(tc->data_edge_descriptors[1], std::make_pair('x', '1'));
  EXPECT_EQ(tc->data_edge_descriptors[2], std::make_pair('Z', '1'));
  EXPECT_EQ(tc->data_edge_descriptors[3], std::make_pair('X', '0'));
}

// edge_descriptor ::= zero_or_one z_or_x ; the leading 0/1 lexes as a separate
// int literal token, so the descriptor uses the split-token parse path.
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
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kEdge);
  ASSERT_EQ(tc->data_edge_descriptors.size(), 4u);
  EXPECT_EQ(tc->data_edge_descriptors[0], std::make_pair('0', 'x'));
  EXPECT_EQ(tc->data_edge_descriptors[1], std::make_pair('1', 'z'));
  EXPECT_EQ(tc->data_edge_descriptors[2], std::make_pair('0', 'z'));
  EXPECT_EQ(tc->data_edge_descriptors[3], std::make_pair('1', 'x'));
}

// timing_check_condition ::= scalar_timing_check_condition ; the bare
// scalar_timing_check_condition ::= expression form after &&&.
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
  ASSERT_NE(tc->ref_condition, nullptr);
}

// timing_check_condition ::= ( scalar_timing_check_condition ) -- parenthesized.
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

// scalar_timing_check_condition ::= ~ expression
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
  ASSERT_NE(tc->ref_condition, nullptr);
  EXPECT_EQ(tc->ref_condition->kind, ExprKind::kUnary);
  EXPECT_EQ(tc->ref_condition->op, TokenKind::kTilde);
}

// scalar_timing_check_condition ::= expression == scalar_constant
// scalar_constant ::= 1'b1
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
  ASSERT_NE(tc->ref_condition, nullptr);
  EXPECT_EQ(tc->ref_condition->kind, ExprKind::kBinary);
  EXPECT_EQ(tc->ref_condition->op, TokenKind::kEqEq);
  EXPECT_NE(tc->ref_condition->rhs, nullptr);
}

// scalar_timing_check_condition ::= expression === scalar_constant
// scalar_constant ::= 1'b0
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
  ASSERT_NE(tc->ref_condition, nullptr);
  EXPECT_EQ(tc->ref_condition->kind, ExprKind::kBinary);
  EXPECT_EQ(tc->ref_condition->op, TokenKind::kEqEqEq);
}

// scalar_timing_check_condition ::= expression != scalar_constant
// scalar_constant ::= 'b1
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
  ASSERT_NE(tc->ref_condition, nullptr);
  EXPECT_EQ(tc->ref_condition->kind, ExprKind::kBinary);
  EXPECT_EQ(tc->ref_condition->op, TokenKind::kBangEq);
}

// scalar_timing_check_condition ::= expression !== scalar_constant
// scalar_constant ::= 1 (bare decimal form).
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
  ASSERT_NE(tc->ref_condition, nullptr);
  EXPECT_EQ(tc->ref_condition->kind, ExprKind::kBinary);
  EXPECT_EQ(tc->ref_condition->op, TokenKind::kBangEqEq);
}

// edge_descriptor enumerates a closed set (01|10|z_or_x zero_or_one|
// zero_or_one z_or_x); a token outside it — here "00", whose two digits match
// and so satisfy neither zero_or_one zero_or_one form — must be rejected.
TEST(TimingCheckEventDefParsing, EdgeDescriptorInvalidRejected) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge[01, 00] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// edge_control_specifier with a bracketed list requires at least one
// edge_descriptor; an empty list must be rejected.
TEST(TimingCheckEventDefParsing, EdgeControlSpecifierEmptyListRejected) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge[] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}
