#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// Syntax 20-17: system_call ::= $system ( [ "terminal_command_line" ] ). With a
// terminal command line present, $system parses as a system call whose callee
// is $system and whose single argument is the command string.
TEST(SystemCall, ParsesWithStringArgument) {
  auto r =
      Parse("module m; initial $system(\"mv design.v adder.v\"); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$system");
  ASSERT_EQ(stmt->expr->args.size(), 1u);
  ASSERT_NE(stmt->expr->args[0], nullptr);
  EXPECT_EQ(stmt->expr->args[0]->kind, ExprKind::kStringLiteral);
}

// Syntax 20-17: the terminal_command_line is optional, so $system parses with
// an empty argument list as well.
TEST(SystemCall, ParsesWithNoArgument) {
  auto r = Parse("module m; initial $system(); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$system");
  EXPECT_EQ(stmt->expr->args.size(), 0u);
}

}  // namespace
