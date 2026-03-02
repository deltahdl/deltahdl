// §11.5.1: Vector bit-select and part-select addressing

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult11g {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11g Parse(const std::string& src) {
  ParseResult11g result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult11g& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Expr* FirstAssignRhs(ParseResult11g& r) {
  auto* stmt = FirstInitialStmt(r);
  if (!stmt) return nullptr;
  return stmt->rhs;
}

namespace {

// =========================================================================
// LRM section 11.4.1 -- Vector bit-select and part-select addressing
// =========================================================================
// --- Bit-select with constant index ---
TEST(ParserSection11, Sec11_4_1_BitSelectConstantIndex) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] vec;\n"
      "  initial x = vec[3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
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
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] vec;\n"
      "  initial x = vec[idx];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->index_end, nullptr);
}

// --- Bit-select with expression index (a+b) ---
TEST(ParserSection11, Sec11_4_1_BitSelectExpressionIndex) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] vec;\n"
      "  initial x = vec[a + b];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->index->op, TokenKind::kPlus);
  EXPECT_EQ(rhs->index_end, nullptr);
}

struct ParseResult10d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult10d Parse(const std::string& src) {
  ParseResult10d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult10d& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// --- 7. Blocking assignment to part-select: a[7:4] = 4'hF ---
TEST(ParserSection10, Sec10_4_1_PartSelect) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] a;\n"
      "  initial begin\n"
      "    a[7:4] = 4'hF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->lhs->index_end, nullptr);
}

// --- Constant part-select [7:0] ---
TEST(ParserSection11, Sec11_4_1_ConstPartSelectDescending) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] vec;\n"
      "  initial x = vec[7:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
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
  auto r = Parse(
      "module t;\n"
      "  logic [0:15] vec;\n"
      "  initial x = vec[0:7];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_FALSE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

// --- Indexed part-select up with variable base ---
TEST(ParserSection11, Sec11_4_1_IndexedPartSelectUpVariableBase) {
  auto r = Parse(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  initial x = vec[offset +: 8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
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
  auto r = Parse(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  initial x = vec[offset -: 8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_minus);
  EXPECT_FALSE(rhs->is_part_select_plus);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->index_end, nullptr);
}

struct ParseResult9h {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9h Parse(const std::string& src) {
  ParseResult9h result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// ---------------------------------------------------------------------------
// 16. always_comb with bit select on LHS
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_BitSelectLHS) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic val;\n"
      "  always_comb data[3] = val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->lhs, nullptr);
  EXPECT_EQ(item->body->lhs->kind, ExprKind::kSelect);
}

// =============================================================================
// A.8.4 Primaries — range_expression
// =============================================================================
// § range_expression — expression (simple index)
TEST(ParserA84, RangeExpressionSimpleIndex) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic x;\n"
      "  initial x = data[0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

// § range_expression — part_select_range
TEST(ParserA84, RangeExpressionPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial x = data[7:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_NE(rhs->index_end, nullptr);
}

struct ParseResult7e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult7e Parse(const std::string& src) {
  ParseResult7e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult7e& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

// --- Packed struct bit-select ---
TEST(ParserSection7, Sec7_2_1_PackedBitSelect) {
  auto r = Parse(
      "module t;\n"
      "  struct packed {\n"
      "    bit [7:0] a;\n"
      "    bit [7:0] b;\n"
      "  } s;\n"
      "  initial x = s[0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSelect);
}

// ---------------------------------------------------------------------------
// 17. always_comb with part select on LHS
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_PartSelectLHS) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] bus;\n"
      "  logic [7:0] low_byte;\n"
      "  always_comb bus[7:0] = low_byte;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->lhs, nullptr);
  EXPECT_EQ(item->body->lhs->kind, ExprKind::kSelect);
  EXPECT_NE(item->body->lhs->index, nullptr);
  EXPECT_NE(item->body->lhs->index_end, nullptr);
}

struct ParseResult11f {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static Expr* FirstAssignLhs(ParseResult11f& r) {
  auto* stmt = FirstInitialStmt(r);
  if (!stmt) return nullptr;
  return stmt->lhs;
}

// --- Part-select on LHS of blocking assignment ---
TEST(ParserSection11, Sec11_4_1_PartSelectOnLhsBlocking) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] vec;\n"
      "  initial vec[7:0] = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* lhs = FirstAssignLhs(r);
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(lhs->kind, ExprKind::kSelect);
  ASSERT_NE(lhs->index, nullptr);
  ASSERT_NE(lhs->index_end, nullptr);
  EXPECT_FALSE(lhs->is_part_select_plus);
  EXPECT_FALSE(lhs->is_part_select_minus);
}

// --- Indexed part-select on LHS ---
TEST(ParserSection11, Sec11_4_1_IndexedPartSelectOnLhs) {
  auto r = Parse(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  initial vec[i +: 4] = 4'hA;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* lhs = FirstAssignLhs(r);
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(lhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(lhs->is_part_select_plus);
  ASSERT_NE(lhs->index, nullptr);
  ASSERT_NE(lhs->index_end, nullptr);
}

static ModuleItem* FirstContAssign(ParseResult11g& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) return item;
  }
  return nullptr;
}

// --- Part-select in continuous assignment RHS ---
TEST(ParserSection11, Sec11_4_1_PartSelectInContAssignRhs) {
  auto r = Parse(
      "module t;\n"
      "  wire [15:0] data;\n"
      "  wire [7:0] low;\n"
      "  assign low = data[7:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_rhs, nullptr);
  EXPECT_EQ(ca->assign_rhs->kind, ExprKind::kSelect);
  ASSERT_NE(ca->assign_rhs->index, nullptr);
  ASSERT_NE(ca->assign_rhs->index_end, nullptr);
}

// § constant_range_expression in bit-select context
TEST(ParserA83, ConstantRangeExprBitSelect) {
  auto r = Parse("module m; initial x = data[3]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index_end, nullptr);
}

// § constant_range in part-select context
TEST(ParserA83, ConstantRangePartSelect) {
  auto r = Parse("module m; initial x = data[7:4]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
}

struct ParseResult7 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult7 Parse(const std::string& src) {
  ParseResult7 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult7& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

TEST(ParserSection7, IndexedPartSelectPlus) {
  auto r = Parse(
      "module t;\n"
      "  initial x = data[3 +: 4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
}

TEST(ParserSection7, IndexedPartSelectMinus) {
  auto r = Parse(
      "module t;\n"
      "  initial x = data[7 -: 4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_minus);
}

// =============================================================================
// A.8.3 Expressions — constant_indexed_range / indexed_range
// =============================================================================
// § constant_indexed_range ::= constant_expression +: constant_expression
TEST(ParserA83, IndexedRangePlusColon) {
  auto r = Parse("module m; initial x = data[2+:4]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

// § constant_indexed_range ::= constant_expression -: constant_expression
TEST(ParserA83, IndexedRangeMinusColon) {
  auto r = Parse("module m; initial x = data[7-:4]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_FALSE(rhs->is_part_select_plus);
  EXPECT_TRUE(rhs->is_part_select_minus);
}

// --- Part-select after bit-select a[i][7:0] ---
TEST(ParserSection11, Sec11_4_1_PartSelectAfterBitSelect) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] [7:0] packed_arr;\n"
      "  initial x = packed_arr[1][7:4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kSelect);
  EXPECT_EQ(rhs->base->index_end, nullptr);
}

// § indexed_range with variable base
TEST(ParserA83, IndexedRangeVariableBase) {
  auto r = Parse("module m; initial x = data[i+:8]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
  EXPECT_EQ(rhs->index->kind, ExprKind::kIdentifier);
}

struct ParseResult11d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11d Parse(const std::string& src) {
  ParseResult11d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// --- Bit-select on concatenation (§11.4.12) ---
TEST(ParserSection11, BitSelectOnConcat) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] a, b, c;\n"
      "  initial a = {b, c}[5:2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- Select on member access result (s.field[i]) ---
TEST(ParserSection11, Sec11_4_1_SelectOnMemberAccess) {
  auto r = Parse(
      "module t;\n"
      "  initial x = s.field[2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kMemberAccess);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index_end, nullptr);
}

static ModuleItem* FirstAlwaysCombItem(ParseResult11g& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock) return item;
  }
  return nullptr;
}

// --- Indexed part-select in always_comb ---
TEST(ParserSection11, Sec11_4_1_IndexedPartSelectInAlwaysComb) {
  auto r = Parse(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  logic [7:0] out;\n"
      "  always_comb out = vec[8 +: 8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysCombItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(item->body->rhs->is_part_select_plus);
}

TEST(ParserAnnexA, A8BitAndPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = data[3]; y = data[7:4]; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- Part-select with system function as index ($clog2) ---
TEST(ParserSection11, Sec11_4_1_PartSelectWithSysFuncIndex) {
  auto r = Parse(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  initial x = vec[$clog2(16):0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kSystemCall);
  ASSERT_NE(rhs->index_end, nullptr);
}

// --- Multiple part-selects in expression ---
TEST(ParserSection11, Sec11_4_1_MultiplePartSelectsInExpr) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  initial x = a[7:0] | b[15:8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
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
  auto r = Parse(
      "module t;\n"
      "  logic [63:0] vec;\n"
      "  initial x = vec[(i * 8) +: 8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->index->op, TokenKind::kStar);
}

struct ParseResult11e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11e Parse(const std::string& src) {
  ParseResult11e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult11e& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Expr* FirstAssignRhs(ParseResult11e& r) {
  auto* stmt = FirstInitialStmt(r);
  if (!stmt) return nullptr;
  return stmt->rhs;
}

// =========================================================================
// Section 11.5.1 -- Bit-select
// =========================================================================
TEST(ParserSection11, BitSelectWithExprIndex) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a[i + 1];\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kBinary);
}

// =============================================================================
// A.8.4 Primaries — bit_select
// =============================================================================
// § bit_select — single dimension
TEST(ParserA84, BitSelectSingleDim) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic x;\n"
      "  initial x = data[5];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index_end, nullptr);
}

// --- Part-select in if condition ---
TEST(ParserSection11, Sec11_4_1_PartSelectInIfCondition) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  initial begin\n"
      "    if (data[3:0] == 4'hF) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
  ASSERT_NE(stmt->condition->lhs, nullptr);
  EXPECT_EQ(stmt->condition->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->condition->lhs->index_end, nullptr);
}

// --- Packed struct indexed part-select plus ---
TEST(ParserSection7, Sec7_2_1_PackedIndexedPartSelectPlus) {
  auto r = Parse(
      "module t;\n"
      "  struct packed {\n"
      "    bit [7:0] a;\n"
      "    bit [7:0] b;\n"
      "    bit [7:0] c;\n"
      "    bit [7:0] d;\n"
      "  } s;\n"
      "  initial x = s[8 +: 8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(stmt->rhs->is_part_select_plus);
}

// =============================================================================
// A.8.4 Primaries — select
// =============================================================================
// § select — bit_select with part_select_range
TEST(ParserA84, SelectBitWithPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  logic [31:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial x = data[15:8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
}

// =========================================================================
// Section 11.5.2 -- Part-select
// =========================================================================
TEST(ParserSection11, PartSelectHasIndexEnd) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a[15:8];\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_NE(rhs->index, nullptr);
  EXPECT_NE(rhs->index_end, nullptr);
}

// =============================================================================
// A.8.3 Expressions — part_select_range / constant_part_select_range
// =============================================================================
// § part_select_range ::= constant_range
TEST(ParserA83, PartSelectConstantRange) {
  auto r = Parse("module m; initial x = data[15:8]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_FALSE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

// § part_select_range ::= indexed_range (+:)
TEST(ParserA83, PartSelectIndexedPlus) {
  auto r = Parse("module m; initial x = data[0+:8]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
}

}  // namespace
