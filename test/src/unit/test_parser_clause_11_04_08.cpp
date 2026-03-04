// §11.4.8: Bitwise operators

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// --- 5. Blocking assignment with bitwise AND expression ---
TEST(ParserSection10, Sec10_4_1_ExprBitwiseAnd) {
  auto r = Parse("module m;\n"
                 "  reg [7:0] a, b, c;\n"
                 "  initial begin\n"
                 "    a = b & c;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}
TEST(ParserSection11, XnorBinaryOperator) {
  auto r = Parse("module t;\n"
                 "  initial x = a ^~ b;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kCaretTilde);
}

// =============================================================================
// A.8.6 Operators — binary_operator (bitwise)
// =============================================================================
// § binary_operator ::= &
TEST(ParserA86, BinaryBitwiseAnd) {
  auto r = Parse("module m; initial x = a & b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

// § binary_operator ::= |
TEST(ParserA86, BinaryBitwiseOr) {
  auto r = Parse("module m; initial x = a | b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
}

// § binary_operator ::= ^
TEST(ParserA86, BinaryBitwiseXor) {
  auto r = Parse("module m; initial x = a ^ b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
}

// § binary_operator ::= ^~
TEST(ParserA86, BinaryBitwiseXnor) {
  auto r = Parse("module m; initial x = a ^~ b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kCaretTilde);
}

// § binary_operator ::= ~^
TEST(ParserA86, BinaryBitwiseXnorAlt) {
  auto r = Parse("module m; initial x = a ~^ b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeCaret);
}

// § expression ::= unary_operator { attribute_instance } primary
TEST(ParserA83, ExprUnaryOp) {
  auto r = Parse("module m; initial x = ~a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
}

// § unary_operator ::= ~
TEST(ParserA86, UnaryBitwiseNot) {
  auto r = Parse("module m; initial x = ~a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
}

// --- Unary operators ---
TEST(ParserSection11, Sec11_1_UnaryBitwiseNot) {
  auto r = Parse("module t;\n"
                 "  initial x = ~b;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
}

// --- Binary operators overview ---
TEST(ParserSection11, Sec11_1_BinaryXnorTildeCaret) {
  auto r = Parse("module t;\n"
                 "  initial x = a ~^ b;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeCaret);
}

// --- Expressions in different contexts ---
TEST(ParserSection11, Sec11_1_ExprInContinuousAssign) {
  auto r = Parse("module t;\n"
                 "  wire a, b, c;\n"
                 "  assign c = a ^ b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ModuleItem *ca = nullptr;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      ca = item;
      break;
    }
  }
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_rhs, nullptr);
  EXPECT_EQ(ca->assign_rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(ca->assign_rhs->op, TokenKind::kCaret);
}
// =========================================================================
// Section 11.4.8 -- Bitwise operators
// =========================================================================
TEST(ParserSection11, BitwiseAnd) {
  auto r = Parse("module t;\n"
                 "  initial x = a & b;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

TEST(ParserSection11, BitwiseOr) {
  auto r = Parse("module t;\n"
                 "  initial x = a | b;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
}

TEST(ParserSection11, BitwiseXor) {
  auto r = Parse("module t;\n"
                 "  initial x = a ^ b;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
}

TEST(ParserSection11, BitwiseNot) {
  auto r = Parse("module t;\n"
                 "  initial x = ~a;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
}

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
TEST(ParserCh505, Operator_UnaryBitwiseNegate) {
  auto r = Parse("module m;\n"
                 "  initial x = ~y;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
}

} // namespace
