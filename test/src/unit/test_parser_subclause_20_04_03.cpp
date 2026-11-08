#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(TimeformatSysTask, BareInvocationParsesAsArglessSystemCall) {
  auto r = Parse("module m; initial $timeformat; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$timeformat");
  EXPECT_TRUE(stmt->expr->args.empty());
}

TEST(TimeformatSysTask, FullInvocationParsesFourArguments) {
  auto r =
      Parse("module m; initial $timeformat(-9, 5, \" ns\", 10); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$timeformat");
  ASSERT_EQ(stmt->expr->args.size(), 4u);
  EXPECT_EQ(stmt->expr->args[2]->kind, ExprKind::kStringLiteral);
}

}  // namespace
