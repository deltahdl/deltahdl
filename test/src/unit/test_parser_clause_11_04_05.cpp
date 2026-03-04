// §11.4.5: Equality operators

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

// § binary_operator ::= !==
TEST(ParserA86, BinaryCaseNeq) {
  auto r = Parse("module m; initial x = (a !== b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kBangEqEq);
}
// =========================================================================
// Section 11.3.5 -- Equality operators
// =========================================================================
TEST(ParserSection11, EqualityInComplexExpr) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a == b) && (c != d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
}

TEST(ParserSection11, CaseEqualityInAssign) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a === 4'bx01z) ? 1 : 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
}
// =========================================================================
// Section 11.4.5 -- Equality operators
// =========================================================================
TEST(ParserSection11, EqualityEq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a == b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kEqEq);
}

TEST(ParserSection11, EqualityNeq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a != b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kBangEq);
}

TEST(ParserSection11, CaseEqualityEq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a === b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kEqEqEq);
}

TEST(ParserSection11, CaseEqualityNeq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a !== b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kBangEqEq);
}

// Comparison operators
TEST(ParserA83, ExprEquality) {
  auto r = Parse("module m; initial x = (a == b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEq);
}

TEST(ParserA83, ExprCaseEquality) {
  auto r = Parse("module m; initial x = (a === b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEqEq);
}

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
TEST(ParserCh505, Operator_CaseEquality) {
  // === is the case equality operator.
  auto r = Parse(
      "module m;\n"
      "  initial x = (a === b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEqEq);
}

TEST(ParserCh505, Operator_CaseInequality) {
  // !== is the case inequality operator.
  EXPECT_TRUE(ParseOk("module m; initial x = (a !== b); endmodule"));
}

}  // namespace
