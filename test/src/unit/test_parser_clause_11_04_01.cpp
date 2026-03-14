#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ProceduralBlockSyntaxParsing, OperatorAssignment_PlusEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a += 1; end\n"
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

TEST(ProceduralBlockSyntaxParsing, OperatorAssignment_MinusEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a -= 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kMinusEq);
}

TEST(ProceduralBlockSyntaxParsing, OperatorAssignment_StarEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a *= 2; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kStarEq);
}

TEST(ProceduralBlockSyntaxParsing, OperatorAssignment_SlashEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a /= 2; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kSlashEq);
}

TEST(ProceduralBlockSyntaxParsing, OperatorAssignment_PercentEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a %= 3; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kPercentEq);
}

TEST(ProceduralBlockSyntaxParsing, OperatorAssignment_AmpEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a &= 8'hFF; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kAmpEq);
}

TEST(ProceduralBlockSyntaxParsing, OperatorAssignment_PipeEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a |= 8'h01; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kPipeEq);
}

TEST(ProceduralBlockSyntaxParsing, OperatorAssignment_CaretEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a ^= 8'hAA; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kCaretEq);
}

TEST(ProceduralBlockSyntaxParsing, OperatorAssignment_LeftShiftEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a <<= 2; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kLtLtEq);
}

TEST(ProceduralBlockSyntaxParsing, OperatorAssignment_RightShiftEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a >>= 2; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kGtGtEq);
}

TEST(ProceduralBlockSyntaxParsing, OperatorAssignment_ArithLeftShiftEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a <<<= 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kLtLtLtEq);
}

TEST(ProceduralBlockSyntaxParsing, OperatorAssignment_ArithRightShiftEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a >>>= 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kGtGtGtEq);
}

TEST(ProceduralBlockSyntaxParsing, OperatorAssignment_WithSelectLhs) {
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

TEST(ProceduralBlockSyntaxParsing, AssignmentOperator_AllThirteen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    a += 1;\n"
      "    a -= 1;\n"
      "    a *= 2;\n"
      "    a /= 2;\n"
      "    a %= 3;\n"
      "    a &= 8'hFF;\n"
      "    a |= 8'h01;\n"
      "    a ^= 8'hAA;\n"
      "    a <<= 1;\n"
      "    a >>= 1;\n"
      "    a <<<= 1;\n"
      "    a >>>= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto stmts = AllInitialStmts(r);
  ASSERT_EQ(stmts.size(), 13u);

  for (auto* s : stmts) {
    EXPECT_EQ(s->kind, StmtKind::kBlockingAssign);
  }
}

TEST(ProceduralBlockSyntaxParsing, Integration_AlwaysCombWithOperatorAssign) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin\n"
      "    sum = a + b;\n"
      "    sum += carry_in;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysCombBlock);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
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

TEST(OperatorAndExpressionParsing, CompoundAssignPlusEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a += 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);

  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(OperatorAndExpressionParsing, CompoundAssignMinusEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a -= 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(OperatorAndExpressionParsing, CompoundAssignStarEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a *= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, CompoundAssignSlashEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a /= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, CompoundAssignPercentEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a %= 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, CompoundAssignAmpEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a &= 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, CompoundAssignPipeEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a |= 8'h0F;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, CompoundAssignCaretEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a ^= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, CompoundAssignLtLtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a <<= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, CompoundAssignGtGtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a >>= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, CompoundAssignLtLtLtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a <<<= 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, CompoundAssignGtGtGtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a >>>= 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
TEST(ProceduralAssignAndControlParsing, BlockingAssignCompound) {
  auto r = Parse(
      "module m;\n"
      "  initial x += 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

}  // namespace
