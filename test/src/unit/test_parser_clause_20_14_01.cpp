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

}  // namespace
