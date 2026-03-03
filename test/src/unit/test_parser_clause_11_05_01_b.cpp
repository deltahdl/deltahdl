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

// --- Multiple bit-selects in concatenation ---
TEST(ParserSection11, Sec11_4_1_BitSelectsInConcatenation) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial x = {data[7], data[6], data[5], data[4]};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 4u);
  for (auto* elem : rhs->elements) {
    EXPECT_EQ(elem->kind, ExprKind::kSelect);
    EXPECT_EQ(elem->index_end, nullptr);
  }
}

// --- Indexed part-select with parameter width ---
TEST(ParserSection11, Sec11_4_1_IndexedPartSelectParamWidth) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  parameter W = 8;\n"
              "  logic [31:0] vec;\n"
              "  initial x = vec[0 +: W];\n"
              "endmodule\n"));
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

TEST(ParserSection11, IndexedPartSelectVariableBase) {
  auto r = Parse(
      "module t;\n"
      "  logic [63:0] dword;\n"
      "  integer sel;\n"
      "  initial x = dword[8*sel +: 8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
}

// --- Bit-select ---
TEST(ParserSection11, Sec11_1_BitSelectIndex) {
  auto r = Parse(
      "module t;\n"
      "  initial x = data[7];\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
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
  auto* rhs = FirstAssignRhs(r);
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
  auto* rhs = FirstAssignRhs(r);
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
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_minus);
  EXPECT_FALSE(rhs->is_part_select_plus);
}

}  // namespace
