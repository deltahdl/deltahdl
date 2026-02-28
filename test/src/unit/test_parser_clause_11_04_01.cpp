// §11.4.1: Assignment operators

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// Return all statements from the first initial block's begin/end.
static std::vector<Stmt*> AllInitialStmts(ParseResult& r) {
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  if (!item || !item->body) return {};
  if (item->body->kind == StmtKind::kBlock) return item->body->stmts;
  return {item->body};
}

namespace {

// =============================================================================
// A.6.2 Production: operator_assignment
// operator_assignment ::= variable_lvalue assignment_operator expression
// =============================================================================
TEST(ParserA602, OperatorAssignment_PlusEq) {
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

TEST(ParserA602, OperatorAssignment_MinusEq) {
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

TEST(ParserA602, OperatorAssignment_StarEq) {
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

TEST(ParserA602, OperatorAssignment_SlashEq) {
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

TEST(ParserA602, OperatorAssignment_PercentEq) {
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

TEST(ParserA602, OperatorAssignment_AmpEq) {
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

TEST(ParserA602, OperatorAssignment_PipeEq) {
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

TEST(ParserA602, OperatorAssignment_CaretEq) {
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

TEST(ParserA602, OperatorAssignment_LeftShiftEq) {
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

TEST(ParserA602, OperatorAssignment_RightShiftEq) {
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

TEST(ParserA602, OperatorAssignment_ArithLeftShiftEq) {
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

TEST(ParserA602, OperatorAssignment_ArithRightShiftEq) {
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

TEST(ParserA602, OperatorAssignment_WithSelectLhs) {
  // Compound assignment with array/bit-select LHS
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

// =============================================================================
// A.6.2 Production: assignment_operator
// assignment_operator ::= = | += | -= | *= | /= | %= | &= | |= | ^=
//                        | <<= | >>= | <<<= | >>>=
// (The simple '=' is tested by blocking_assignment tests above; compound
// operators are tested by operator_assignment tests above. This section
// tests that all 13 operators work correctly in sequence.)
// =============================================================================
TEST(ParserA602, AssignmentOperator_AllThirteen) {
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
  // All should be blocking assignments
  for (auto* s : stmts) {
    EXPECT_EQ(s->kind, StmtKind::kBlockingAssign);
  }
}

}  // namespace
