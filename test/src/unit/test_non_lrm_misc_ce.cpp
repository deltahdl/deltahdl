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

TEST(ParserLet, InstantiationDefaultArgs) {
  auto r = Parse(
      "module t;\n"
      "  let at_least_two(sig, rst = 1'b0) = rst || sig;\n"
      "  initial begin\n"
      "    logic [15:0] sig1;\n"
      "    logic q;\n"
      "    q = at_least_two(sig1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ==========================================================================
// §11.12: Let in package scope
// ==========================================================================
TEST(ParserLet, DeclInPackage) {
  auto r = Parse(
      "package pkg;\n"
      "  let my_op(x, y) = x & y;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.2.8 block_item_declaration alternative 4: let_declaration
TEST(ParserA28, LetDeclInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    let my_add(x, y) = x + y;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA28, LetDeclNoArgsInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    let val = 42;\n"
              "  end\n"
              "endmodule\n"));
}

// let_declaration in task body
TEST(ParserA28, LetDeclInTask) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task my_task();\n"
              "    let inc(x) = x + 1;\n"
              "  endtask\n"
              "endmodule\n"));
}

// let_declaration in fork/join
TEST(ParserA28, LetDeclInForkJoin) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    let val = 99;\n"
              "  join\n"
              "endmodule\n"));
}

TEST(ParserA210, AssertionItemDecl_LetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let max(a, b) = (a > b) ? a : b;\n"
              "endmodule\n"));
}

// =========================================================================
// Section 11.3.6 -- Assignment operators in expressions
// =========================================================================
TEST(ParserSection11, CompoundAssignPlusEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a += 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  // Compound assignment is parsed as blocking assign with op
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection11, CompoundAssignMinusEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a -= 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection11, CompoundAssignStarEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a *= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignSlashEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a /= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignPercentEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a %= 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignAmpEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a &= 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignPipeEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a |= 8'h0F;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

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
