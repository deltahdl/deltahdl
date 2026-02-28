// §11.4.7: Logical operators

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.8.6 Operators — binary_operator (logical)
// =============================================================================
// § binary_operator ::= &&
TEST(ParserA86, BinaryLogicalAnd) {
  auto r = Parse("module m; initial x = (a && b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
}

// § binary_operator ::= ||
TEST(ParserA86, BinaryLogicalOr) {
  auto r = Parse("module m; initial x = (a || b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPipePipe);
}

// =============================================================================
// A.8.6 Operators — binary_operator (implication)
// =============================================================================
// § binary_operator ::= ->
TEST(ParserA86, BinaryImplication) {
  auto r = Parse("module m; initial x = (a -> b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kArrow);
}

}  // namespace
