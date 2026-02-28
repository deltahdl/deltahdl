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

}  // namespace
