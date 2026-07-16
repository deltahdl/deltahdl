#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// IEEE 1800-2023 §9.4.2.2 — the parser recognizes the implicit event control
// @* and its parenthesized spelling @(*) and marks the construct as the star
// form (is_star_sensitivity on a module-level always item, is_star_event on a
// procedural event-control statement). The statement that follows the control
// is parsed by the ordinary statement grammar and is not part of this rule, so
// these tests cover only the distinct syntactic forms of @* itself: bare vs.
// parenthesized, in a module always vs. in a procedural statement, and the
// nested inner @* of LRM Example 4.

TEST(ImplicitEventParsing, AtStarAlwaysSimple) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  always @* a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

TEST(ImplicitEventParsing, AtStarParenAlwaysSimple) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  always @(*) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

TEST(ImplicitEventParsing, AtStarStmtLevelInitial) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @* a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

TEST(ImplicitEventParsing, AtStarParenStmtLevel) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @(*) a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

TEST(ImplicitEventParsing, NestedAtStarParsesAsEventControl) {
  // LRM Example 4: an inner @* inside an @* always body parses as its own
  // event-control statement (is_star_event). Also exercises @* preceding a
  // begin/end block.
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c, d, x;\n"
      "  always @* begin\n"
      "    x = a ^ b;\n"
      "    @* x = c ^ d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 2u);
  auto* nested = item->body->stmts[1];
  EXPECT_EQ(nested->kind, StmtKind::kEventControl);
  EXPECT_TRUE(nested->is_star_event);
  EXPECT_TRUE(nested->events.empty());
  ASSERT_NE(nested->body, nullptr);
  EXPECT_EQ(nested->body->kind, StmtKind::kBlockingAssign);
}

}  // namespace
