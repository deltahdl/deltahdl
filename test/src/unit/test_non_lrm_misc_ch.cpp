// Non-LRM tests

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

static ModuleItem* FirstContAssign(ParseResult11g& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) return item;
  }
  return nullptr;
}

namespace {

// --- Indexed part-select with parameter width ---
TEST(ParserSection11, Sec11_4_1_IndexedPartSelectParamWidth) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  parameter W = 8;\n"
              "  logic [31:0] vec;\n"
              "  initial x = vec[0 +: W];\n"
              "endmodule\n"));
}

// =========================================================================
// LRM section 11.4.6 -- Conditional operator (ternary ? :)
// =========================================================================
// --- Simple ternary: sel ? a : b ---
TEST(ParserSection11, Sec11_4_6_SimpleTernary) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  VerifyTernaryFieldsAllIdentifier(rhs);
}

// --- Ternary in continuous assignment ---
TEST(ParserSection11, Sec11_4_6_TernaryInContAssign) {
  auto r = Parse(
      "module t;\n"
      "  wire sel, a, b, y;\n"
      "  assign y = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_rhs, nullptr);
  EXPECT_EQ(ca->assign_rhs->kind, ExprKind::kTernary);
  ASSERT_NE(ca->assign_rhs->condition, nullptr);
  EXPECT_EQ(ca->assign_rhs->condition->kind, ExprKind::kIdentifier);
  ASSERT_NE(ca->assign_rhs->true_expr, nullptr);
  ASSERT_NE(ca->assign_rhs->false_expr, nullptr);
}

// --- Ternary in blocking assignment ---
TEST(ParserSection11, Sec11_4_6_TernaryInBlockingAssign) {
  auto r = Parse(
      "module t;\n"
      "  initial y = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

// --- Ternary in nonblocking assignment ---
TEST(ParserSection11, Sec11_4_6_TernaryInNonblockingAssign) {
  auto r = Parse(
      "module t;\n"
      "  reg q;\n"
      "  initial q <= sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

// --- Nested ternary with parentheses ---
TEST(ParserSection11, Sec11_4_6_NestedTernaryWithParens) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel1 ? (sel2 ? a : b) : c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kIdentifier);
}

// --- Chained ternary without parens (right-associative) ---
TEST(ParserSection11, Sec11_4_6_ChainedTernaryRightAssoc) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel1 ? a : sel2 ? b : c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kIdentifier);
  // Right-associative: false_expr is itself a ternary.
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr->true_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->true_expr->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->false_expr->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->false_expr->kind, ExprKind::kIdentifier);
}

// --- Ternary with complex condition ---
TEST(ParserSection11, Sec11_4_6_TernaryWithComplexCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a > b) ? y : z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->condition->op, TokenKind::kGt);
}

// --- Ternary with binary expression operands ---
TEST(ParserSection11, Sec11_4_6_TernaryWithBinaryOperands) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? (a + b) : (c - d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->true_expr->op, TokenKind::kPlus);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->false_expr->op, TokenKind::kMinus);
}

// --- Ternary with function call operands ---
TEST(ParserSection11, Sec11_4_6_TernaryWithFuncCallOperands) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? func(a) : func(b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kCall);
  EXPECT_EQ(rhs->true_expr->callee, "func");
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kCall);
}

// --- Ternary with concatenation operands ---
TEST(ParserSection11, Sec11_4_6_TernaryWithConcatenationOperands) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? {a, b} : {c, d};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->true_expr->elements.size(), 2u);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->false_expr->elements.size(), 2u);
}

// --- Ternary with replication operands ---
TEST(ParserSection11, Sec11_4_6_TernaryWithReplication) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? {4{a}} : {4{b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kReplicate);
  ASSERT_NE(rhs->true_expr->repeat_count, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kReplicate);
}

// --- Ternary with bit-select operands ---
TEST(ParserSection11, Sec11_4_6_TernaryWithBitSelectOperands) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial x = sel ? a[3] : b[3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kSelect);
  EXPECT_EQ(rhs->true_expr->index_end, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kSelect);
  EXPECT_EQ(rhs->false_expr->index_end, nullptr);
}

// --- Ternary with part-select operands ---
TEST(ParserSection11, Sec11_4_6_TernaryWithPartSelectOperands) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial x = sel ? a[7:4] : b[7:4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->true_expr->index, nullptr);
  ASSERT_NE(rhs->true_expr->index_end, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->false_expr->index_end, nullptr);
}

// --- Ternary in if condition ---
TEST(ParserSection11, Sec11_4_6_TernaryInIfCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (sel ? a : b) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kTernary);
}

}  // namespace
