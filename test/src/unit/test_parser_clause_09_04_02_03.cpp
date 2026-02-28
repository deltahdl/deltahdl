// §9.4.2.3: Conditional event controls

#include "fixture_parser.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// iff guard with comma-separated events at statement level
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardCommaStmtLevel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk iff en, negedge rst) q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 2u);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
  EXPECT_EQ(stmt->events[1].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with or-separated events at statement level
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardOrStmtLevel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk iff en or negedge rst) q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 2u);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
  EXPECT_EQ(stmt->events[1].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard in always_ff context
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardAlwaysFF) {
  auto r = Parse(
      "module m;\n"
      "  always_ff @(posedge clock iff reset == 0 or posedge reset) begin\n"
      "    r1 <= reset ? 0 : r2 + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysFFBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_EQ(item->sensitivity.size(), 2u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kPosedge);
  EXPECT_EQ(item->sensitivity[1].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with begin-end body
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff en) begin\n"
      "    a <= b;\n"
      "    c <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_GE(item->body->stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// Verify iff_condition field is populated for posedge
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffConditionFieldPosedge) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff reset == 0) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  const auto& ev = item->sensitivity[0];
  // The iff_condition should be an equality comparison expression.
  ASSERT_NE(ev.iff_condition, nullptr);
  EXPECT_EQ(ev.iff_condition->kind, ExprKind::kBinary);
}

// ---------------------------------------------------------------------------
// Verify signal field is populated
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_SignalFieldPopulated) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff en) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  const auto& ev = item->sensitivity[0];
  ASSERT_NE(ev.signal, nullptr);
  EXPECT_EQ(ev.signal->kind, ExprKind::kIdentifier);
  EXPECT_EQ(ev.signal->text, "clk");
}

// ---------------------------------------------------------------------------
// Verify edge field for negedge with iff
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_EdgeFieldNegedge) {
  auto r = Parse(
      "module m;\n"
      "  always @(negedge rst_n iff mode) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kNegedge);
  ASSERT_NE(item->sensitivity[0].signal, nullptr);
  EXPECT_EQ(item->sensitivity[0].signal->text, "rst_n");
}

// ---------------------------------------------------------------------------
// Multiple event expressions with mixed iff presence
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_MixedIffPresence) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff en, negedge rst, edge sig iff guard)\n"
      "    q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 3u);
  // First: posedge clk iff en
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
  // Second: negedge rst (no iff)
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kNegedge);
  EXPECT_EQ(item->sensitivity[1].iff_condition, nullptr);
  // Third: edge sig iff guard
  EXPECT_EQ(item->sensitivity[2].edge, Edge::kEdge);
  EXPECT_NE(item->sensitivity[2].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with logical-or condition expression
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardLogicalOr) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff (a || b)) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with not-equal comparison
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardNotEqual) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff state != 0) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  ASSERT_NE(item->sensitivity[0].iff_condition, nullptr);
  EXPECT_EQ(item->sensitivity[0].iff_condition->kind, ExprKind::kBinary);
}

// ---------------------------------------------------------------------------
// iff guard at always_ff level with single posedge (no reset)
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardAlwaysFFSingleEdge) {
  auto r = Parse(
      "module m;\n"
      "  always_ff @(posedge clk iff en)\n"
      "    q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysFFBlock);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard on no-edge event at statement level with comparison
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardNoEdgeStmtComparison) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(data iff enable == 1) y = data;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// iff guard with unary negation in guard expression
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardUnaryNegation) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff !bypass) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  ASSERT_NE(item->sensitivity[0].iff_condition, nullptr);
  EXPECT_EQ(item->sensitivity[0].iff_condition->kind, ExprKind::kUnary);
}

// ---------------------------------------------------------------------------
// iff guard with bitwise-and in guard expression
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardBitwiseAnd) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff (mask & enable)) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// ParseOk: three events all with iff guards (or-separated)
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardThreeEventsOr) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  always @(posedge a iff g1 or negedge b iff g2 or edge c iff g3)\n"
      "    q <= d;\n"
      "endmodule\n"));
}

// ---------------------------------------------------------------------------
// ParseOk: iff guard in always block with nonblocking assignment
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardNonblockingAssign) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk iff valid)\n"
              "    data_out <= data_in;\n"
              "endmodule\n"));
}

// ---------------------------------------------------------------------------
// Verify iff condition absent when not specified
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_NoIffConditionWhenAbsent) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_EQ(item->sensitivity[0].iff_condition, nullptr);
}

// ---------------------------------------------------------------------------
// Verify body is preserved under iff guard at statement level
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardStmtLevelBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(negedge clk iff active) begin\n"
      "      a = 1;\n"
      "      b = 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
  EXPECT_GE(stmt->body->stmts.size(), 2u);
}

}  // namespace
