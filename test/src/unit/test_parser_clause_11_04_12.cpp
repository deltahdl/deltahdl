// §11.4.12: Concatenation operators

#include "fixture_parser.h"

using namespace delta;

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

namespace {

// ---------------------------------------------------------------------------
// 13. always_comb with concatenation
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_Concatenation) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] c;\n"
      "  always_comb c = {a, b};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(item->body->rhs->elements.size(), 2u);
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
// Section 11.4.12 -- Concatenation operators
// =========================================================================
TEST(ParserSection11, ConcatWithPartSelects) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a, w, b;\n"
      "  initial x = {a, b[3:0], w, 3'b101};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 4u);
}

TEST(ParserAnnexA, A8Concatenation) {
  auto r = Parse("module m; initial x = {a, b, c}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 3u);
}

// ---------------------------------------------------------------------------
// 27. always_comb with concatenation on LHS
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_ConcatenationLHS) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] hi, lo;\n"
      "  logic [7:0] data;\n"
      "  always_comb {hi, lo} = data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->lhs, nullptr);
  EXPECT_EQ(item->body->lhs->kind, ExprKind::kConcatenation);
}

TEST(ParserSection11, ConcatOnLhsOfAssign) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic log1, log2, log3;\n"
              "  initial {log1, log2, log3} = 3'b111;\n"
              "endmodule\n"));
}

}  // namespace
