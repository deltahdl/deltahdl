#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserCh513, BuiltInMethod_PushBack) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q.push_back(42);\n"
              "endmodule"));
}

TEST(ParserSection7, QueueMethodPushBack) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q.push_back(42);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection7, QueuePushBack) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q.push_back(42);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

}
