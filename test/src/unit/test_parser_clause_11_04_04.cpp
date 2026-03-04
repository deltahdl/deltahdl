// §11.4.4: Relational operators

#include "fixture_parser.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

// =============================================================================
// A.8.6 Operators — binary_operator (relational)
// =============================================================================
// § binary_operator ::= <
TEST(ParserA86, BinaryLessThan) {
  auto r = Parse("module m; initial x = (a < b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLt);
}

// § binary_operator ::= <=
TEST(ParserA86, BinaryLessOrEqual) {
  auto r = Parse("module m; initial x = (a <= b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtEq);
}

// § binary_operator ::= >
TEST(ParserA86, BinaryGreaterThan) {
  auto r = Parse("module m; initial x = (a > b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGt);
}

// § binary_operator ::= >=
TEST(ParserA86, BinaryGreaterOrEqual) {
  auto r = Parse("module m; initial x = (a >= b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGtEq);
}
// =========================================================================
// Section 11.4.4 -- Relational operators
// =========================================================================
TEST(ParserSection11, RelationalLt) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a < b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kLt);
}

TEST(ParserSection11, RelationalGt) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a > b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kGt);
}

TEST(ParserSection11, RelationalLtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a <= b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kLtEq);
}

TEST(ParserSection11, RelationalGtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a >= b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kGtEq);
}

TEST(Eval, Comparison) {
  ExprFixture f;
  auto* expr = ParseExprFrom("5 > 3", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

}  // namespace
