#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

struct ParseResult10b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult10b Parse(const std::string& src) {
  ParseResult10b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static Stmt* FirstInitialStmt(ParseResult10b& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Stmt* NthInitialStmt(ParseResult10b& r, size_t n) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      if (n < item->body->stmts.size()) return item->body->stmts[n];
    }
  }
  return nullptr;
}

static ModuleItem* FindItemByKind(const std::vector<ModuleItem*>& items,
                                  ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// =============================================================================
// LRM section 10.1 -- Overview of procedural assignments
// =============================================================================

TEST(ParserSection10, OverviewBlockingAssignWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #10 a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection10, OverviewNonblockingAssignWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #5 a <= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection10, OverviewMultipleBlockingStmts) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "    c = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 3u);
}

// =============================================================================
// LRM section 10.3 -- Continuous assignments
// =============================================================================

TEST(ParserSection10, ContAssignBitwiseAnd) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] a, b, c;\n"
      "  assign c = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* ca = FindItemByKind(r.cu->modules[0]->items,
                            ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_rhs, nullptr);
  EXPECT_EQ(ca->assign_rhs->kind, ExprKind::kBinary);
}

TEST(ParserSection10, ContAssignConcatOnLhs) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c;\n"
      "  assign {a, b} = {c, c};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* ca = FindItemByKind(r.cu->modules[0]->items,
                            ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kConcatenation);
}

TEST(ParserSection10, ContAssignReplication) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] out;\n"
      "  wire in;\n"
      "  assign out = {8{in}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* ca = FindItemByKind(r.cu->modules[0]->items,
                            ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_rhs, nullptr);
  EXPECT_EQ(ca->assign_rhs->kind, ExprKind::kReplicate);
}

// =============================================================================
// LRM section 10.8 -- Operator assignments (additional tests)
// =============================================================================

TEST(ParserSection10, OpAssignPlusEqWithBinaryExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a += b + c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection10, OpAssignBitwiseOps) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data &= 8'hF0;\n"
      "    data |= 8'h0F;\n"
      "    data ^= 8'hAA;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection10, OpAssignShiftOps) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  logic [15:0] val;\n"
      "  initial begin\n"
      "    val <<= 4;\n"
      "    val >>= 2;\n"
      "    val <<<= 1;\n"
      "    val >>>= 3;\n"
      "  end\n"
      "endmodule\n"));
}

// =============================================================================
// LRM section 10.9 -- Modifying assignment operators (pre-increment/decrement)
// =============================================================================

TEST(ParserSection10, PreIncrementStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial ++a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kUnary);
  EXPECT_EQ(stmt->expr->op, TokenKind::kPlusPlus);
}

TEST(ParserSection10, PreDecrementStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial --a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kUnary);
  EXPECT_EQ(stmt->expr->op, TokenKind::kMinusMinus);
}

// =============================================================================
// LRM section 10.9.1 -- Increment and decrement (postfix forms)
// =============================================================================

TEST(ParserSection10, PostIncrementStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial a++;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(stmt->expr->op, TokenKind::kPlusPlus);
}

TEST(ParserSection10, PostDecrementStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial a--;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(stmt->expr->op, TokenKind::kMinusMinus);
}

TEST(ParserSection10, IncrementInForLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) begin\n"
      "      a = i;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
}

// =============================================================================
// LRM section 10.9.2 -- Assignment within expressions
// =============================================================================

TEST(ParserSection10, PostIncrementAsRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    b = a++;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kPostfixUnary);
}

TEST(ParserSection10, PreIncrementAsRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    b = ++a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kUnary);
}

TEST(ParserSection10, PostIncrementArrayElement) {
  auto r = Parse(
      "module m;\n"
      "  int arr[4];\n"
      "  initial arr[0]++;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kPostfixUnary);
}

// =============================================================================
// LRM section 10.10 -- Unpacked array concatenation
// =============================================================================

TEST(ParserSection10, UnpackedConcatTwoArrays) {
  auto r = Parse(
      "module m;\n"
      "  int A[2] = '{1, 2};\n"
      "  int B[2] = '{3, 4};\n"
      "  int C[4];\n"
      "  initial C = {A, B};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
}

TEST(ParserSection10, UnpackedConcatToQueueElements) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 3u);
}

TEST(ParserSection10, UnpackedConcatQueueAppend) {
  auto r = Parse(
      "module m;\n"
      "  int q[$] = '{1, 2};\n"
      "  initial q = {q, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
}

// =============================================================================
// LRM section 10.1 -- Mixed blocking and nonblocking assignments
// =============================================================================

TEST(ParserSection10, MixedBlockingAndNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b <= 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s1->kind, StmtKind::kNonblockingAssign);
}

// =============================================================================
// LRM section 10.3 -- Continuous assignment with conditional expression
// =============================================================================

TEST(ParserSection10, ContAssignTernary) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, sel, y;\n"
      "  assign y = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* ca = FindItemByKind(r.cu->modules[0]->items,
                            ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_rhs, nullptr);
  EXPECT_EQ(ca->assign_rhs->kind, ExprKind::kTernary);
}

TEST(ParserSection10, ContAssignUnaryNot) {
  auto r = Parse(
      "module m;\n"
      "  wire a, y;\n"
      "  assign y = ~a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* ca = FindItemByKind(r.cu->modules[0]->items,
                            ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_rhs, nullptr);
  EXPECT_EQ(ca->assign_rhs->kind, ExprKind::kUnary);
}

// =============================================================================
// LRM section 10.8 -- Operator assignment with complex RHS
// =============================================================================

TEST(ParserSection10, OpAssignWithTernaryRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a += sel ? 1 : 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

// =============================================================================
// LRM section 10.9.1 -- Increment/decrement on array elements
// =============================================================================

TEST(ParserSection10, PreDecrementArrayElement) {
  auto r = Parse(
      "module m;\n"
      "  int arr[4];\n"
      "  initial --arr[2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

// =============================================================================
// LRM section 10.10 -- Unpacked array concatenation (queue prepend)
// =============================================================================

TEST(ParserSection10, UnpackedConcatQueuePrepend) {
  auto r = Parse(
      "module m;\n"
      "  int q[$] = '{2, 3};\n"
      "  initial q = {1, q};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
}

// =============================================================================
// LRM section 10.3 -- Net declaration assignment
// =============================================================================

TEST(ParserSection10, NetDeclAssignLogicVector) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] nibble = 4'b1010;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  auto* item = mod->items[0];
  EXPECT_EQ(item->name, "nibble");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection10, NetDeclAssignMultiple) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  wire a = 1'b0, b = 1'b1;\n"
      "endmodule\n"));
}

// =============================================================================
// LRM section 10.9 -- Assignment patterns (array and struct forms)
// =============================================================================

TEST(ParserSection10, AssignPatternArrayPositional) {
  auto r = Parse(
      "module m;\n"
      "  int A[3] = '{10, 20, 30};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  EXPECT_NE(mod->items[0]->init_expr, nullptr);
  EXPECT_EQ(mod->items[0]->init_expr->kind, ExprKind::kAssignmentPattern);
}

TEST(ParserSection10, AssignPatternArrayReplicated) {
  auto r = Parse(
      "module m;\n"
      "  int A[4] = '{4{0}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  EXPECT_NE(mod->items[0]->init_expr, nullptr);
}

TEST(ParserSection10, AssignPatternArrayDefault) {
  auto r = Parse(
      "module m;\n"
      "  int A[8] = '{default: -1};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  EXPECT_NE(mod->items[0]->init_expr, nullptr);
}

TEST(ParserSection10, AssignPatternStructByName) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  point_t p = '{x: 10, y: 20};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection10, AssignPatternStructDefault) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int x; int y; int z; } vec3_t;\n"
      "  vec3_t v = '{default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection10, AssignPatternNested) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  typedef struct { point_t origin; int radius; } circle_t;\n"
      "  circle_t c = '{origin: '{x: 0, y: 0}, radius: 5};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
