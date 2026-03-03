// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult11 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11 Parse(const std::string& src) {
  ParseResult11 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult11& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

namespace {

TEST(ParserSection11, CompoundAssignCaretEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a ^= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignLtLtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a <<= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignGtGtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a >>= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignLtLtLtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a <<<= 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignGtGtGtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a >>>= 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, PostfixIncrementParses) {
  auto r = Parse(
      "module t;\n"
      "  initial a++;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection11, PostfixIncrementOp) {
  auto r = Parse(
      "module t;\n"
      "  initial a++;\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(stmt->expr->op, TokenKind::kPlusPlus);
}

TEST(ParserSection11, PostfixDecrementParses) {
  auto r = Parse(
      "module t;\n"
      "  initial a--;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection11, PostfixDecrementOp) {
  auto r = Parse(
      "module t;\n"
      "  initial a--;\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(stmt->expr->op, TokenKind::kMinusMinus);
}

// =========================================================================
// Section 11.4.13 -- Inside operator (set membership)
// =========================================================================
TEST(ParserSection11, InsideBasicListParses) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {1, 2, 3}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
}

}  // namespace
