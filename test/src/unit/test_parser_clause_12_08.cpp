#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

static ModuleItem* FindFunc12b(ParseResult& r, std::string_view name) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == name)
      return item;
  }
  return nullptr;
}

TEST(JumpStatementSyntaxParsing, ReturnFromVoidFunctionEarly) {
  auto r = Parse(
      "module t;\n"
      "  function void check(int val);\n"
      "    if (val < 0) return;\n"
      "    $display(\"ok\");\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc12b(r, "check");
  ASSERT_NE(fn, nullptr);
  ASSERT_GE(fn->func_body_stmts.size(), 1u);

  auto* if_stmt = fn->func_body_stmts[0];
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  ASSERT_NE(if_stmt->then_branch, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kReturn);
  EXPECT_EQ(if_stmt->then_branch->expr, nullptr);
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

TEST(JumpStatementSyntaxParsing, BreakStatementInBody) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    forever begin\n"
      "      if (done) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);

  auto* if_stmt = stmt->body->stmts[0];
  ASSERT_NE(if_stmt, nullptr);
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  ASSERT_NE(if_stmt->then_branch, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kBreak);
}

TEST(JumpStatementSyntaxParsing, ContinueStatementInBody) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i = i + 1) begin\n"
      "      if (i == 5) continue;\n"
      "      x = i;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* body = stmt->for_body;
  ASSERT_NE(body, nullptr);
  auto* if_stmt = body->stmts[0];
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kContinue);
}

}
