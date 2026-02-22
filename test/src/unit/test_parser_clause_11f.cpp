#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult11f {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult11f Parse(const std::string &src) {
  ParseResult11f result;
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

static Stmt *FirstInitialStmt(ParseResult11f &r) {
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

static Expr *FirstAssignRhs(ParseResult11f &r) {
  auto *stmt = FirstInitialStmt(r);
  if (!stmt)
    return nullptr;
  return stmt->rhs;
}

static Expr *FirstAssignLhs(ParseResult11f &r) {
  auto *stmt = FirstInitialStmt(r);
  if (!stmt)
    return nullptr;
  return stmt->lhs;
}

static ModuleItem *FirstContAssign(ParseResult11f &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign)
      return item;
  }
  return nullptr;
}

static ModuleItem *FirstAlwaysCombItem(ParseResult11f &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock)
      return item;
  }
  return nullptr;
}

// =========================================================================
// LRM section 11.4.1 -- Vector bit-select and part-select addressing
// =========================================================================

// --- Bit-select with constant index ---

TEST(ParserSection11, Sec11_4_1_BitSelectConstantIndex) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] vec;\n"
                 "  initial x = vec[3];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->index_end, nullptr);
  EXPECT_FALSE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

// --- Bit-select with variable index ---

TEST(ParserSection11, Sec11_4_1_BitSelectVariableIndex) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] vec;\n"
                 "  initial x = vec[idx];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->index_end, nullptr);
}

// --- Bit-select with expression index (a+b) ---

TEST(ParserSection11, Sec11_4_1_BitSelectExpressionIndex) {
  auto r = Parse("module t;\n"
                 "  logic [15:0] vec;\n"
                 "  initial x = vec[a + b];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->index->op, TokenKind::kPlus);
  EXPECT_EQ(rhs->index_end, nullptr);
}

// --- Constant part-select [7:0] ---

TEST(ParserSection11, Sec11_4_1_ConstPartSelectDescending) {
  auto r = Parse("module t;\n"
                 "  logic [15:0] vec;\n"
                 "  initial x = vec[7:0];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_FALSE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

// --- Constant part-select [0:7] (ascending range) ---

TEST(ParserSection11, Sec11_4_1_ConstPartSelectAscending) {
  auto r = Parse("module t;\n"
                 "  logic [0:15] vec;\n"
                 "  initial x = vec[0:7];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_FALSE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

// --- Indexed part-select up with variable base ---

TEST(ParserSection11, Sec11_4_1_IndexedPartSelectUpVariableBase) {
  auto r = Parse("module t;\n"
                 "  logic [31:0] vec;\n"
                 "  initial x = vec[offset +: 8];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_EQ(rhs->index_end->kind, ExprKind::kIntegerLiteral);
}

// --- Indexed part-select down with variable base ---

TEST(ParserSection11, Sec11_4_1_IndexedPartSelectDownVariableBase) {
  auto r = Parse("module t;\n"
                 "  logic [31:0] vec;\n"
                 "  initial x = vec[offset -: 8];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_minus);
  EXPECT_FALSE(rhs->is_part_select_plus);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->index_end, nullptr);
}

// --- Bit-select on LHS of blocking assignment ---

TEST(ParserSection11, Sec11_4_1_BitSelectOnLhsBlocking) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] vec;\n"
                 "  initial vec[3] = 1'b1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  auto *lhs = FirstAssignLhs(r);
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(lhs->kind, ExprKind::kSelect);
  ASSERT_NE(lhs->base, nullptr);
  EXPECT_EQ(lhs->base->kind, ExprKind::kIdentifier);
  ASSERT_NE(lhs->index, nullptr);
  EXPECT_EQ(lhs->index_end, nullptr);
}

// --- Part-select on LHS of blocking assignment ---

TEST(ParserSection11, Sec11_4_1_PartSelectOnLhsBlocking) {
  auto r = Parse("module t;\n"
                 "  logic [15:0] vec;\n"
                 "  initial vec[7:0] = 8'hFF;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *lhs = FirstAssignLhs(r);
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(lhs->kind, ExprKind::kSelect);
  ASSERT_NE(lhs->index, nullptr);
  ASSERT_NE(lhs->index_end, nullptr);
  EXPECT_FALSE(lhs->is_part_select_plus);
  EXPECT_FALSE(lhs->is_part_select_minus);
}

// --- Indexed part-select on LHS ---

TEST(ParserSection11, Sec11_4_1_IndexedPartSelectOnLhs) {
  auto r = Parse("module t;\n"
                 "  logic [31:0] vec;\n"
                 "  initial vec[i +: 4] = 4'hA;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *lhs = FirstAssignLhs(r);
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(lhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(lhs->is_part_select_plus);
  ASSERT_NE(lhs->index, nullptr);
  ASSERT_NE(lhs->index_end, nullptr);
}

// --- Bit-select on LHS of nonblocking assignment ---

TEST(ParserSection11, Sec11_4_1_BitSelectOnLhsNonblocking) {
  auto r = Parse("module t;\n"
                 "  reg [7:0] vec;\n"
                 "  initial vec[5] <= 1'b0;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  EXPECT_EQ(stmt->lhs->index_end, nullptr);
}

// --- Part-select in continuous assignment RHS ---

TEST(ParserSection11, Sec11_4_1_PartSelectInContAssignRhs) {
  auto r = Parse("module t;\n"
                 "  wire [15:0] data;\n"
                 "  wire [7:0] low;\n"
                 "  assign low = data[7:0];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_rhs, nullptr);
  EXPECT_EQ(ca->assign_rhs->kind, ExprKind::kSelect);
  ASSERT_NE(ca->assign_rhs->index, nullptr);
  ASSERT_NE(ca->assign_rhs->index_end, nullptr);
}

// --- Bit-select in continuous assignment LHS ---

TEST(ParserSection11, Sec11_4_1_BitSelectInContAssignLhs) {
  auto r = Parse("module t;\n"
                 "  wire [7:0] vec;\n"
                 "  wire val;\n"
                 "  assign vec[0] = val;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kSelect);
  EXPECT_EQ(ca->assign_lhs->index_end, nullptr);
}

// --- Nested bit-selects a[i][j] ---

TEST(ParserSection11, Sec11_4_1_NestedBitSelects) {
  auto r = Parse("module t;\n"
                 "  logic [3:0] [7:0] packed_arr;\n"
                 "  initial x = packed_arr[2][3];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_EQ(rhs->index_end, nullptr);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kSelect);
  EXPECT_EQ(rhs->base->index_end, nullptr);
}

// --- Part-select after bit-select a[i][7:0] ---

TEST(ParserSection11, Sec11_4_1_PartSelectAfterBitSelect) {
  auto r = Parse("module t;\n"
                 "  logic [3:0] [7:0] packed_arr;\n"
                 "  initial x = packed_arr[1][7:4];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kSelect);
  EXPECT_EQ(rhs->base->index_end, nullptr);
}

// --- Select on member access result (s.field[i]) ---

TEST(ParserSection11, Sec11_4_1_SelectOnMemberAccess) {
  auto r = Parse("module t;\n"
                 "  initial x = s.field[2];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kMemberAccess);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index_end, nullptr);
}

// --- Select on concatenation result ({a,b}[i]) ---

TEST(ParserSection11, Sec11_4_1_SelectOnConcatenation) {
  auto r = Parse("module t;\n"
                 "  initial x = {a, b}[3];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->index_end, nullptr);
}

// --- Indexed part-select in always_comb ---

TEST(ParserSection11, Sec11_4_1_IndexedPartSelectInAlwaysComb) {
  auto r = Parse("module t;\n"
                 "  logic [31:0] vec;\n"
                 "  logic [7:0] out;\n"
                 "  always_comb out = vec[8 +: 8];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysCombItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(item->body->rhs->is_part_select_plus);
}

// --- Part-select with system function as index ($clog2) ---

TEST(ParserSection11, Sec11_4_1_PartSelectWithSysFuncIndex) {
  auto r = Parse("module t;\n"
                 "  logic [31:0] vec;\n"
                 "  initial x = vec[$clog2(16):0];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kSystemCall);
  ASSERT_NE(rhs->index_end, nullptr);
}

// --- Multiple part-selects in expression ---

TEST(ParserSection11, Sec11_4_1_MultiplePartSelectsInExpr) {
  auto r = Parse("module t;\n"
                 "  logic [15:0] a, b;\n"
                 "  initial x = a[7:0] | b[15:8];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->lhs->index_end, nullptr);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->rhs->index_end, nullptr);
}

// --- Indexed part-select with complex base expression ---

TEST(ParserSection11, Sec11_4_1_IndexedPartSelectComplexBase) {
  auto r = Parse("module t;\n"
                 "  logic [63:0] vec;\n"
                 "  initial x = vec[(i * 8) +: 8];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->index->op, TokenKind::kStar);
}

// --- Bit-select in ternary condition ---

TEST(ParserSection11, Sec11_4_1_BitSelectInTernaryCondition) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] flags;\n"
                 "  initial x = flags[0] ? a : b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->kind, ExprKind::kSelect);
  EXPECT_EQ(rhs->condition->index_end, nullptr);
}

// --- Part-select in if condition ---

TEST(ParserSection11, Sec11_4_1_PartSelectInIfCondition) {
  auto r = Parse("module t;\n"
                 "  logic [15:0] data;\n"
                 "  initial begin\n"
                 "    if (data[3:0] == 4'hF) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
  ASSERT_NE(stmt->condition->lhs, nullptr);
  EXPECT_EQ(stmt->condition->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->condition->lhs->index_end, nullptr);
}

// --- Bit-select assigned from function call ---

TEST(ParserSection11, Sec11_4_1_BitSelectAssignedFromFuncCall) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] vec;\n"
                 "  initial vec[0] = get_bit();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

// --- Indexed part-select in for loop ---

TEST(ParserSection11, Sec11_4_1_IndexedPartSelectInForLoop) {
  EXPECT_TRUE(ParseOk("module t;\n"
                      "  logic [31:0] data;\n"
                      "  logic [7:0] bytes [4];\n"
                      "  initial begin\n"
                      "    for (int i = 0; i < 4; i++)\n"
                      "      bytes[i] = data[i*8 +: 8];\n"
                      "  end\n"
                      "endmodule\n"));
}

// --- Indexed part-select down on LHS ---

TEST(ParserSection11, Sec11_4_1_IndexedPartSelectDownOnLhs) {
  auto r = Parse("module t;\n"
                 "  logic [31:0] vec;\n"
                 "  initial vec[j -: 4] = 4'b1010;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *lhs = FirstAssignLhs(r);
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(lhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(lhs->is_part_select_minus);
  EXPECT_FALSE(lhs->is_part_select_plus);
  ASSERT_NE(lhs->index, nullptr);
  ASSERT_NE(lhs->index_end, nullptr);
}

// --- Select on function return value ---

TEST(ParserSection11, Sec11_4_1_SelectOnFuncReturnValue) {
  auto r = Parse("module t;\n"
                 "  initial x = get_data()[7:0];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kCall);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
}

// --- Select on system function result ---

TEST(ParserSection11, Sec11_4_1_SelectOnSystemFuncResult) {
  EXPECT_TRUE(ParseOk("module t;\n"
                      "  initial x = $random[3:0];\n"
                      "endmodule\n"));
}

// --- Multiple bit-selects in concatenation ---

TEST(ParserSection11, Sec11_4_1_BitSelectsInConcatenation) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] data;\n"
                 "  initial x = {data[7], data[6], data[5], data[4]};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 4u);
  for (auto *elem : rhs->elements) {
    EXPECT_EQ(elem->kind, ExprKind::kSelect);
    EXPECT_EQ(elem->index_end, nullptr);
  }
}

// --- Indexed part-select with parameter width ---

TEST(ParserSection11, Sec11_4_1_IndexedPartSelectParamWidth) {
  EXPECT_TRUE(ParseOk("module t;\n"
                      "  parameter W = 8;\n"
                      "  logic [31:0] vec;\n"
                      "  initial x = vec[0 +: W];\n"
                      "endmodule\n"));
}
