#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §20.14.1, Syntax 20-14: random_function ::= $random [ ( seed ) ]. The seed is
// optional, so a bare $random with no argument list is a well-formed call.
TEST(RandomFunctionParsing, NoSeedArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $random;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->callee, "$random");
  EXPECT_TRUE(stmt->rhs->args.empty());
}

// §20.14.1, Syntax 20-14: the optional ( seed ) form supplies one argument that
// selects the random stream.
TEST(RandomFunctionParsing, WithSeedArgument) {
  auto r = Parse(
      "module m;\n"
      "  integer seed;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->callee, "$random");
  ASSERT_EQ(stmt->rhs->args.size(), 1u);
}

// §20.14.1, Syntax 20-14: the $random call is a primary, so it may appear as an
// operand embedded in a larger expression rather than only as a whole
// right-hand side — here as the left operand of a modulus, the shape the
// clause's own example uses. The system call parses as the binary operator's
// left operand.
TEST(RandomFunctionParsing, AppearsAsExpressionOperand) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $random % 60;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kPercent);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
  EXPECT_EQ(stmt->rhs->lhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->lhs->callee, "$random");
}

}  // namespace
