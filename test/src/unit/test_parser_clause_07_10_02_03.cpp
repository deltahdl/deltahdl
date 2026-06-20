#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(AggregateTypeParsing, QueueDeleteMethodWithIndex) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q.delete(0);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

TEST(AggregateTypeParsing, QueueDeleteMethodNoArg) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q.delete();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

TEST(AggregateTypeParsing, QueueDeletePropertyStyle) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q.delete;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
