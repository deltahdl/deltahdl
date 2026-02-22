#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult11e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult11e Parse(const std::string &src) {
  ParseResult11e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static Stmt *FirstInitialStmt(ParseResult11e &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Expr *FirstAssignRhs(ParseResult11e &r) {
  auto *stmt = FirstInitialStmt(r);
  if (!stmt) return nullptr;
  return stmt->rhs;
}

// =========================================================================
// LRM section 11.1 -- Operators and operands overview
// =========================================================================

// --- Primary operand types ---

TEST(ParserSection11, Sec11_1_IdentifierAsExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = foo;\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
}

TEST(ParserSection11, Sec11_1_StringLiteralAsExpression) {
  auto r = Parse(
      "module t;\n"
      "  string s;\n"
      "  initial s = \"hello world\";\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

TEST(ParserSection11, Sec11_1_RealLiteralAsExpression) {
  auto r = Parse(
      "module t;\n"
      "  real r;\n"
      "  initial r = 3.14;\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

// --- Call expressions ---

TEST(ParserSection11, Sec11_1_SystemFunctionCallExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = $clog2(256);\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$clog2");
}

TEST(ParserSection11, Sec11_1_FunctionCallExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = my_func(a, b);\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
  EXPECT_EQ(rhs->callee, "my_func");
  EXPECT_EQ(rhs->args.size(), 2u);
}

// --- Member access ---

TEST(ParserSection11, Sec11_1_MemberAccessExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = obj.field;\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
}

// --- Parenthesized expression ---

TEST(ParserSection11, Sec11_1_ParenthesizedExprPreservesSemantics) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a + b) * c;\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPlus);
}

// --- Unary operators ---

TEST(ParserSection11, Sec11_1_UnaryBitwiseNot) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ~b;\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
}

TEST(ParserSection11, Sec11_1_UnaryLogicalNot) {
  auto r = Parse(
      "module t;\n"
      "  initial x = !flag;\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kBang);
}

TEST(ParserSection11, Sec11_1_UnaryReductionNand) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ~&data;\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeAmp);
}

TEST(ParserSection11, Sec11_1_UnaryReductionNor) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ~|data;\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildePipe);
}

TEST(ParserSection11, Sec11_1_UnaryReductionXnorTildeCaret) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ~^data;\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeCaret);
}

TEST(ParserSection11, Sec11_1_UnaryReductionXnorCaretTilde) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ^~data;\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kCaretTilde);
}

// --- Binary operators overview ---

TEST(ParserSection11, Sec11_1_BinaryXnorTildeCaret) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a ~^ b;\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeCaret);
}

TEST(ParserSection11, Sec11_1_BinaryPowerOperator) {
  auto r = Parse(
      "module t;\n"
      "  initial x = base ** exp;\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPower);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

// --- Ternary conditional expression ---

TEST(ParserSection11, Sec11_1_TernaryConditionalFields) {
  auto r = Parse(
      "module t;\n"
      "  initial x = en ? val_a : val_b;\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kIdentifier);
}

// --- Concatenation ---

TEST(ParserSection11, Sec11_1_ConcatenationElements) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {a, b, 1'b0};\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 3u);
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->elements[2]->kind, ExprKind::kIntegerLiteral);
}

// --- Replication ---

TEST(ParserSection11, Sec11_1_ReplicateRepeatCountAndElements) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {3{a, b}};\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
  ASSERT_NE(rhs->repeat_count, nullptr);
  EXPECT_EQ(rhs->repeat_count->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->elements.size(), 2u);
}

// --- Bit-select ---

TEST(ParserSection11, Sec11_1_BitSelectIndex) {
  auto r = Parse(
      "module t;\n"
      "  initial x = data[7];\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->index_end, nullptr);
}

// --- Part-select ---

TEST(ParserSection11, Sec11_1_PartSelectIndexAndEnd) {
  auto r = Parse(
      "module t;\n"
      "  initial x = data[15:0];\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_FALSE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

// --- Indexed part-select +: and -: ---

TEST(ParserSection11, Sec11_1_IndexedPartSelectPlusFlag) {
  auto r = Parse(
      "module t;\n"
      "  initial x = vec[i +: 4];\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
}

TEST(ParserSection11, Sec11_1_IndexedPartSelectMinusFlag) {
  auto r = Parse(
      "module t;\n"
      "  initial x = vec[j -: 8];\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_minus);
  EXPECT_FALSE(rhs->is_part_select_plus);
}

// --- Cast expression ---

TEST(ParserSection11, Sec11_1_CastExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = int'(3.14);\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

// --- Assignment pattern ---

TEST(ParserSection11, Sec11_1_AssignmentPatternExpression) {
  auto r = Parse(
      "module t;\n"
      "  int arr[3];\n"
      "  initial arr = '{1, 2, 3};\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

// --- Streaming concatenation ---

TEST(ParserSection11, Sec11_1_StreamingConcatLeftShift) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {<< {a, b}};\n"
      "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
  EXPECT_EQ(rhs->elements.size(), 2u);
}

// --- Postfix increment/decrement ---

TEST(ParserSection11, Sec11_1_PostfixIncrementExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial counter++;\n"
      "endmodule\n");
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(stmt->expr->op, TokenKind::kPlusPlus);
}

TEST(ParserSection11, Sec11_1_PostfixDecrementExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial counter--;\n"
      "endmodule\n");
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(stmt->expr->op, TokenKind::kMinusMinus);
}

// --- Inside expression ---

TEST(ParserSection11, Sec11_1_InsideExpressionWithLhsAndElements) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (val inside {1, 2, 3}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
  ASSERT_NE(cond->lhs, nullptr);
  EXPECT_EQ(cond->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(cond->elements.size(), 3u);
}

// --- Expressions in different contexts ---

TEST(ParserSection11, Sec11_1_ExprInContinuousAssign) {
  auto r = Parse(
      "module t;\n"
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

TEST(ParserSection11, Sec11_1_ExprInInitialBlock) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a | b) & c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

TEST(ParserSection11, Sec11_1_ExprAsFunctionArgument) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(a + b, c * d, {e, f});\n"
              "endmodule\n"));
}

// --- Additional all-operator coverage ---

TEST(ParserSection11, Sec11_1_AllBinaryOperatorsParse) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    x = a + b;\n"
              "    x = a - b;\n"
              "    x = a * b;\n"
              "    x = a / b;\n"
              "    x = a % b;\n"
              "    x = a ** b;\n"
              "    x = a == b;\n"
              "    x = a != b;\n"
              "    x = a === b;\n"
              "    x = a !== b;\n"
              "    x = a < b;\n"
              "    x = a <= b;\n"
              "    x = a > b;\n"
              "    x = a >= b;\n"
              "    x = a && b;\n"
              "    x = a || b;\n"
              "    x = a & b;\n"
              "    x = a | b;\n"
              "    x = a ^ b;\n"
              "    x = a ~^ b;\n"
              "    x = a ^~ b;\n"
              "    x = a << b;\n"
              "    x = a >> b;\n"
              "    x = a <<< b;\n"
              "    x = a >>> b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection11, Sec11_1_AllUnaryOperatorsParse) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    x = +a;\n"
              "    x = -a;\n"
              "    x = ~a;\n"
              "    x = !a;\n"
              "    x = &a;\n"
              "    x = |a;\n"
              "    x = ^a;\n"
              "    x = ~&a;\n"
              "    x = ~|a;\n"
              "    x = ~^a;\n"
              "    x = ^~a;\n"
              "  end\n"
              "endmodule\n"));
}
