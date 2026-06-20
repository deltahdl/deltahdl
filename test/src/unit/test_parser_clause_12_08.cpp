#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Parse a multi-dimensional foreach body and verify its common structure,
// returning the inner if-statement so the caller can assert on its branch.
static Stmt* MultiDimForeachIfStmt(const char* src, ParseResult& r) {
  r = Parse(src);
  EXPECT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_NE(stmt, nullptr);
  if (stmt == nullptr) return nullptr;
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_GE(stmt->foreach_vars.size(), 2u);
  auto* blk = stmt->body;
  EXPECT_NE(blk, nullptr);
  if (blk == nullptr) return nullptr;
  EXPECT_GE(blk->stmts.size(), 1u);
  if (blk->stmts.empty()) return nullptr;
  auto* if_stmt = blk->stmts[0];
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  EXPECT_NE(if_stmt->then_branch, nullptr);
  return if_stmt;
}

TEST(JumpStatementSyntaxParsing, BreakInsideWhile) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    while (1) begin\n"
      "      if (done) break;\n"
      "      x = x + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  auto* blk = stmt->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_GE(blk->stmts.size(), 1u);
  auto* if_stmt = blk->stmts[0];
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  ASSERT_NE(if_stmt->then_branch, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kBreak);
}

TEST(JumpStatementSyntaxParsing, ContinueInsideDoWhile) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    do begin\n"
      "      if (skip) continue;\n"
      "      x = x + 1;\n"
      "    end while (x < 10);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  auto* blk = stmt->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_GE(blk->stmts.size(), 1u);
  auto* if_stmt = blk->stmts[0];
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  ASSERT_NE(if_stmt->then_branch, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kContinue);
}

TEST(JumpStatementSyntaxParsing, BreakInsideForeach) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    foreach (arr[i]) begin\n"
      "      if (arr[i] == 0) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  auto* blk = stmt->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_GE(blk->stmts.size(), 1u);
  EXPECT_EQ(blk->stmts[0]->kind, StmtKind::kIf);
  EXPECT_EQ(blk->stmts[0]->then_branch->kind, StmtKind::kBreak);
}

TEST(JumpStatementSyntaxParsing, ContinueInsideForeach) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    foreach (arr[i]) begin\n"
      "      if (arr[i] == 0) continue;\n"
      "      sum = sum + arr[i];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  auto* blk = stmt->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_GE(blk->stmts.size(), 2u);
  auto* if_stmt = blk->stmts[0];
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kContinue);
}

TEST(JumpStatementSyntaxParsing, BreakInsideMultiDimForeach) {
  ParseResult r;
  auto* if_stmt = MultiDimForeachIfStmt(
      "module t;\n"
      "  initial begin\n"
      "    foreach (matrix[i, j]) begin\n"
      "      if (matrix[i][j] == 0) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      r);
  ASSERT_NE(if_stmt, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kBreak);
}

TEST(JumpStatementSyntaxParsing, ContinueInsideMultiDimForeach) {
  ParseResult r;
  auto* if_stmt = MultiDimForeachIfStmt(
      "module t;\n"
      "  initial begin\n"
      "    foreach (matrix[i, j]) begin\n"
      "      if (matrix[i][j] == 0) continue;\n"
      "      sum = sum + matrix[i][j];\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      r);
  ASSERT_NE(if_stmt, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kContinue);
}

TEST(JumpStatementSyntaxParsing, ReturnVoid) {
  auto r = Parse(
      "module t;\n"
      "  function void bar();\n"
      "    return;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* ret = FindReturnStmt(r);
  ASSERT_NE(ret, nullptr);
  EXPECT_EQ(ret->kind, StmtKind::kReturn);
  EXPECT_EQ(ret->expr, nullptr);
}

TEST(JumpStatementSyntaxParsing, ReturnWithExpressionBnf) {
  auto r = Parse(
      "module t;\n"
      "  function int square(int v);\n"
      "    return v * v;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* ret = FindReturnStmt(r);
  ASSERT_NE(ret, nullptr);
  EXPECT_EQ(ret->kind, StmtKind::kReturn);
  ASSERT_NE(ret->expr, nullptr);
}

}  // namespace
