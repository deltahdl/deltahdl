#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult11d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult11d Parse(const std::string &src) {
  ParseResult11d result;
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

static Stmt *FirstInitialStmt(ParseResult11d &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock)
      continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Expr *FirstAssignRhs(ParseResult11d &r) {
  auto *stmt = FirstInitialStmt(r);
  if (!stmt)
    return nullptr;
  return stmt->rhs;
}

// =========================================================================
// Section 11.1 -- Overview: general expression parsing
// =========================================================================

TEST(ParserSection11, NestedParenthesizedExpression) {
  auto r = Parse("module t;\n"
                 "  initial x = ((a + b) * (c - d));\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
}

TEST(ParserSection11, ComplexMixedExpressionParses) {
  EXPECT_TRUE(ParseOk("module t;\n"
                      "  initial x = (a + b) * c - d / e % f;\n"
                      "endmodule\n"));
}

TEST(ParserSection11, LiteralAsExpression) {
  auto r = Parse("module t;\n"
                 "  initial x = 42;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// =========================================================================
// Section 11.2.1 -- Constant expressions (operands)
// =========================================================================

TEST(ParserSection11, ConstExprInParamDecl) {
  auto r = Parse("module t;\n"
                 "  parameter WIDTH = 8;\n"
                 "  parameter DEPTH = 2 ** WIDTH;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, ConstExprSystemFuncInParam) {
  auto r = Parse("module t;\n"
                 "  parameter N = 16;\n"
                 "  parameter BITS = $clog2(N);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, ConstExprTernaryInLocalparam) {
  auto r = Parse("module t #(parameter A = 1);\n"
                 "  localparam B = (A > 0) ? 10 : 20;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =========================================================================
// Section 11.3 -- Operators (general syntax and unary +)
// =========================================================================

TEST(ParserSection11, UnaryPlusOperator) {
  auto r = Parse("module t;\n"
                 "  initial x = +a;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
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

TEST(ParserSection11, ChainedAdditiveLeftAssoc) {
  auto r = Parse("module t;\n"
                 "  initial x = a + b - c + d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

// =========================================================================
// Section 11.3.1 -- Arithmetic operators with real operands
// =========================================================================

TEST(ParserSection11, RealLiteralAddition) {
  auto r = Parse("module t;\n"
                 "  real r;\n"
                 "  initial r = 1.5 + 2.5;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kRealLiteral);
}

TEST(ParserSection11, RealLiteralWithExponent) {
  auto r = Parse("module t;\n"
                 "  real r;\n"
                 "  initial r = 1.0e3 + 2.5e-1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, RealMultiplication) {
  auto r = Parse("module t;\n"
                 "  real r;\n"
                 "  initial r = 3.14 * 2.0;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
}

// =========================================================================
// Section 11.3.5 -- Equality operators
// =========================================================================

TEST(ParserSection11, EqualityInComplexExpr) {
  auto r = Parse("module t;\n"
                 "  initial x = (a == b) && (c != d);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
}

TEST(ParserSection11, CaseEqualityInAssign) {
  auto r = Parse("module t;\n"
                 "  initial x = (a === 4'bx01z) ? 1 : 0;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
}

// =========================================================================
// Section 11.4.1 -- Replication operator
// =========================================================================

TEST(ParserSection11, ReplicationCountAndElements) {
  auto r = Parse("module t;\n"
                 "  initial x = {4{a}};\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
  ASSERT_NE(rhs->repeat_count, nullptr);
  EXPECT_EQ(rhs->repeat_count->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->elements.size(), 1u);
}

TEST(ParserSection11, ReplicationNestedInConcat) {
  auto r = Parse("module t;\n"
                 "  initial x = {b, {3{a, b}}};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 2u);
  EXPECT_EQ(rhs->elements[1]->kind, ExprKind::kReplicate);
}

TEST(ParserSection11, ReplicationMultipleElements) {
  auto r = Parse("module t;\n"
                 "  initial x = {2{a, b, c}};\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

// =========================================================================
// Section 11.4.3.1 -- Unary reduction operators
// =========================================================================

TEST(ParserSection11, ReductionXnorCaretTilde) {
  auto r = Parse("module t;\n"
                 "  initial x = ^~a;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kCaretTilde);
}

TEST(ParserSection11, ReductionOnParenthesizedExpr) {
  auto r = Parse("module t;\n"
                 "  initial x = &(a ^ b);\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

// =========================================================================
// Section 11.4.6 -- Conditional operator (ternary)
// =========================================================================

TEST(ParserSection11, TernaryFieldAccess) {
  auto r = Parse("module t;\n"
                 "  initial x = sel ? a : b;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  ASSERT_NE(rhs->true_expr, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
}

TEST(ParserSection11, NestedTernaryRightAssoc) {
  auto r = Parse("module t;\n"
                 "  initial x = a ? b : c ? d : e;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kTernary);
}

TEST(ParserSection11, TernaryTristateDriver) {
  EXPECT_TRUE(ParseOk("module t;\n"
                      "  wire drive_busa;\n"
                      "  wire [15:0] data;\n"
                      "  wire [15:0] busa = drive_busa ? data : 16'bz;\n"
                      "endmodule\n"));
}

// =========================================================================
// Section 11.4.12 -- Concatenation operators
// =========================================================================

TEST(ParserSection11, ConcatWithPartSelects) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] a, w, b;\n"
                 "  initial x = {a, b[3:0], w, 3'b101};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 4u);
}

TEST(ParserSection11, ConcatOnLhsOfAssign) {
  EXPECT_TRUE(ParseOk("module t;\n"
                      "  logic log1, log2, log3;\n"
                      "  initial {log1, log2, log3} = 3'b111;\n"
                      "endmodule\n"));
}

// =========================================================================
// Section 11.4.12.1 -- Concatenation
// =========================================================================

TEST(ParserSection11, ConcatPartSelectPostfix) {
  auto r = Parse("module t;\n"
                 "  byte a, b;\n"
                 "  bit [1:0] c;\n"
                 "  initial c = {a + b}[1:0];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, ConcatSingleElement) {
  auto r = Parse("module t;\n"
                 "  initial x = {a};\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 1u);
}

// =========================================================================
// Section 11.4.12.2 -- Replication (string concatenation and replication)
// =========================================================================

TEST(ParserSection11, StringConcatenation) {
  EXPECT_TRUE(ParseOk("module t;\n"
                      "  string hello, s;\n"
                      "  initial begin\n"
                      "    hello = \"hello\";\n"
                      "    s = {hello, \" \", \"world\"};\n"
                      "  end\n"
                      "endmodule\n"));
}

TEST(ParserSection11, StringReplication) {
  EXPECT_TRUE(ParseOk("module t;\n"
                      "  initial begin\n"
                      "    int n;\n"
                      "    string s;\n"
                      "    n = 3;\n"
                      "    s = {n{\"boo \"}};\n"
                      "  end\n"
                      "endmodule\n"));
}

// =========================================================================
// Section 11.4.13 -- Set membership operator (inside) -- additional
// =========================================================================

TEST(ParserSection11, InsideWithWildcardBits) {
  EXPECT_TRUE(ParseOk("module t;\n"
                      "  logic [2:0] val;\n"
                      "  initial begin\n"
                      "    while (val inside {3'b1?1}) val = val + 1;\n"
                      "  end\n"
                      "endmodule\n"));
}

TEST(ParserSection11, InsideWithDollarRange) {
  EXPECT_TRUE(ParseOk("module t;\n"
                      "  int a;\n"
                      "  initial begin\n"
                      "    if (a inside {[$:10]}) a = 0;\n"
                      "  end\n"
                      "endmodule\n"));
}

TEST(ParserSection11, InsideMixedValuesAndRanges) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    if (a inside {1, [5:10], 20, [30:40]}) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
  EXPECT_EQ(cond->elements.size(), 4u);
}

// =========================================================================
// Section 11.5.1 -- Bit-select
// =========================================================================

TEST(ParserSection11, BitSelectWithExprIndex) {
  auto r = Parse("module t;\n"
                 "  initial x = a[i + 1];\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kBinary);
}

TEST(ParserSection11, BitSelectChained) {
  auto r = Parse("module t;\n"
                 "  initial x = mem[i][j];\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kSelect);
}

// =========================================================================
// Section 11.5.2 -- Part-select
// =========================================================================

TEST(ParserSection11, PartSelectHasIndexEnd) {
  auto r = Parse("module t;\n"
                 "  initial x = a[15:8];\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_NE(rhs->index, nullptr);
  EXPECT_NE(rhs->index_end, nullptr);
}

TEST(ParserSection11, ArrayThenPartSelect) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] twod[0:255][0:255];\n"
                 "  initial x = twod[14][1][3:0];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =========================================================================
// Section 11.5.3 -- Indexed part-select
// =========================================================================

TEST(ParserSection11, IndexedPartSelectPlus) {
  auto r = Parse("module t;\n"
                 "  logic [31:0] a_vect;\n"
                 "  initial x = a_vect[0 +: 8];\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

TEST(ParserSection11, IndexedPartSelectMinus) {
  auto r = Parse("module t;\n"
                 "  logic [31:0] a_vect;\n"
                 "  initial x = a_vect[15 -: 8];\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_minus);
  EXPECT_FALSE(rhs->is_part_select_plus);
}

TEST(ParserSection11, IndexedPartSelectVariableBase) {
  auto r = Parse("module t;\n"
                 "  logic [63:0] dword;\n"
                 "  integer sel;\n"
                 "  initial x = dword[8*sel +: 8];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
}

// =========================================================================
// Section 11.7 -- Minimum, typical, and maximum delay expressions
// =========================================================================

TEST(ParserSection11, MinTypMaxInGateDelay) {
  EXPECT_TRUE(ParseOk("module t;\n"
                      "  wire a, b, c;\n"
                      "  and #(2:3:4) g1(c, a, b);\n"
                      "endmodule\n"));
}

TEST(ParserSection11, MinTypMaxInSpecparam) {
  EXPECT_TRUE(ParseOk("module t(input a, output b);\n"
                      "  specify\n"
                      "    specparam tRise = 1:2:3;\n"
                      "  endspecify\n"
                      "endmodule\n"));
}

// =========================================================================
// Section 11.10 -- String literal expressions and methods
// =========================================================================

TEST(ParserSection11, StringLiteralToVector) {
  auto r = Parse("module t;\n"
                 "  bit [8*14:1] stringvar;\n"
                 "  initial stringvar = \"Hello world\";\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

TEST(ParserSection11, StringConcatToVector) {
  EXPECT_TRUE(ParseOk("module t;\n"
                      "  bit [8*14:1] stringvar;\n"
                      "  initial begin\n"
                      "    stringvar = \"Hello world\";\n"
                      "    stringvar = {stringvar, \"!!!\"};\n"
                      "  end\n"
                      "endmodule\n"));
}

TEST(ParserSection11, StringCompareEquality) {
  EXPECT_TRUE(ParseOk("module t;\n"
                      "  string s1, s2;\n"
                      "  initial begin\n"
                      "    s1 = \"hello\";\n"
                      "    s2 = \"hello\";\n"
                      "    if (s1 == s2) $display(\"equal\");\n"
                      "  end\n"
                      "endmodule\n"));
}
