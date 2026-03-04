// §12.7.2: The repeat loop

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// =============================================================================
// LRM section 12.7 -- Loop statements (additional cases)
// =============================================================================
// Repeat loop with expression (not just a literal).
TEST(ParserSection12, RepeatWithExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    repeat (n + 1) begin\n"
      "      x = x + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
  EXPECT_NE(stmt->condition, nullptr);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

// --- repeat ( expression ) statement_or_null ---
TEST(ParserA608, RepeatLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin repeat (10) @(posedge clk); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
  EXPECT_NE(stmt->condition, nullptr);
}

TEST(ParserA608, RepeatNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin repeat (5) ; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
}

}  // namespace
