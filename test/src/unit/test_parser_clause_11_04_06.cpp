// §11.4.6: Wildcard equality operators

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § binary_operator ::= ==?
TEST(ParserA86, BinaryWildcardEq) {
  auto r = Parse("module m; initial x = (a ==? b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEqQuestion);
}

// § binary_operator ::= !=?
TEST(ParserA86, BinaryWildcardNeq) {
  auto r = Parse("module m; initial x = (a !=? b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kBangEqQuestion);
}
// =========================================================================
// Section 11.4.6 -- Wildcard equality operators
// =========================================================================
TEST(ParserSection11, WildcardEq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a ==? b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kEqEqQuestion);
}

TEST(ParserSection11, WildcardNeq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a !=? b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kBangEqQuestion);
}

TEST(ParserSection11, WildcardEqInIfCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (data ==? 8'b1xx0_xx10)\n"
      "      $display(\"match\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
TEST(ParserCh501, Sec5_1_ThreeCharOperatorWildcardInequality) {
  // Verify !=? parses to the correct token kind.
  auto r = Parse(
      "module m;\n"
      "  initial x = (a !=? b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kBangEqQuestion);
}

TEST(ParserCh505, Operator_WildcardEquality) {
  // ==? is the wildcard equality operator.
  EXPECT_TRUE(ParseOk("module m; initial x = (a ==? b); endmodule"));
}

}  // namespace
