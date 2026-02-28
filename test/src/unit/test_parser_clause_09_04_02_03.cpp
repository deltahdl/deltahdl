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

}  // namespace
