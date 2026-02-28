// §11.4.5: Equality operators

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.8.6 Operators — binary_operator (equality)
// =============================================================================
// § binary_operator ::= ==
TEST(ParserA86, BinaryEq) {
  auto r = Parse("module m; initial x = (a == b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEq);
}

// § binary_operator ::= !=
TEST(ParserA86, BinaryNeq) {
  auto r = Parse("module m; initial x = (a != b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kBangEq);
}

// § binary_operator ::= ===
TEST(ParserA86, BinaryCaseEq) {
  auto r = Parse("module m; initial x = (a === b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEqEq);
}

}  // namespace
