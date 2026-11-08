#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"

using namespace delta;
namespace {

TEST(AggregateTypeParsing, AssocArrayDeleteMethodWithIndex) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  initial aa.delete(\"key\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kCall);
  EXPECT_EQ(stmt->expr->args.size(), 1u);
}

TEST(AggregateTypeParsing, AssocArrayDeleteMethodNoArg) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  initial aa.delete();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kCall);
  EXPECT_TRUE(stmt->expr->args.empty());
}

TEST(AggregateTypeParsing, AssocArrayDeletePropertySyntax) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  initial aa.delete;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kMemberAccess);
}

}  // namespace
