#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(PlaSystemTask, ParsesAsSystemCallWithThreeArguments) {
  auto r = Parse(
      "module m; initial $async$and$array(mem, {a1, a2}, {b1, b2}); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$async$and$array");
  ASSERT_EQ(stmt->expr->args.size(), 3u);
}

TEST(PlaSystemTask, ParsesSingleTermArguments) {
  auto r = Parse("module m; initial $sync$or$plane(mem, ai, bo); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$sync$or$plane");
  ASSERT_EQ(stmt->expr->args.size(), 3u);
  ASSERT_NE(stmt->expr->args[0], nullptr);
  EXPECT_EQ(stmt->expr->args[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->expr->args[0]->text, "mem");
}

}  // namespace
