#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(AssignmentParsing, CompoundAssignWithSelectLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin mem[0] += 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(AssignmentParsing, OperatorAssignSlashEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a /= 4;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignPercentEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a %= 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignAmpEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a &= 8'hFF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignPipeEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a |= 8'h01;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignCaretEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a ^= 8'hAA;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignLtLtEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <<= 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignGtGtEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a >>= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignLtLtLtEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <<<= 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignGtGtGtEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a >>>= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, CompoundPlusEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a += 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kPlusEq);
}

TEST(AssignmentParsing, CompoundMinusEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    count -= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kMinusEq);
}

TEST(AssignmentParsing, CompoundMulDivMod) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    a *= 3;\n"
              "    b /= 4;\n"
              "    c %= 5;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(AssignmentParsing, CompoundBitwise) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a &= 8'hFF;\n"
      "    b |= 8'h01;\n"
      "    c ^= 8'hAA;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  auto* s2 = NthInitialStmt(r, 2);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  ASSERT_NE(s2, nullptr);
  EXPECT_EQ(s0->rhs->op, TokenKind::kAmpEq);
  EXPECT_EQ(s1->rhs->op, TokenKind::kPipeEq);
  EXPECT_EQ(s2->rhs->op, TokenKind::kCaretEq);
}

TEST(AssignmentParsing, CompoundShifts) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <<= 2;\n"
      "    b >>= 1;\n"
      "    c <<<= 3;\n"
      "    d >>>= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  auto* s2 = NthInitialStmt(r, 2);
  auto* s3 = NthInitialStmt(r, 3);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  ASSERT_NE(s2, nullptr);
  ASSERT_NE(s3, nullptr);
  EXPECT_EQ(s0->rhs->op, TokenKind::kLtLtEq);
  EXPECT_EQ(s1->rhs->op, TokenKind::kGtGtEq);
  EXPECT_EQ(s2->rhs->op, TokenKind::kLtLtLtEq);
  EXPECT_EQ(s3->rhs->op, TokenKind::kGtGtGtEq);
}

TEST(LvalueParsing, VarLvalueCompoundAdd) {
  auto r = Parse("module m; int x; initial x += 5; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
}

TEST(LvalueParsing, VarLvalueCompoundBitSelect) {
  auto r = Parse("module m; logic [7:0] x; initial x[3] |= 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

}  // namespace
