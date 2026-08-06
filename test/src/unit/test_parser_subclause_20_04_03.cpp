#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// Syntax 20-5: the parens block is optional, so a bare $timeformat is parsed
// as an expression statement wrapping a system call with no arguments.
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

// Syntax 20-5: when the parens block is present it carries the four arguments
// units_number, precision_number, suffix_string, and minimum_field_width.
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
