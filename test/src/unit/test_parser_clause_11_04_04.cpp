// §11.4.4: Relational operators

#include "fixture_parser.h"

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

}  // namespace
