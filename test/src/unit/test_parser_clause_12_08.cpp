#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(Parser, BreakStatement) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    break;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBreak);
}

TEST(Parser, ContinueStatement) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    continue;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kContinue);
}

TEST(Parser, ReturnStatement) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    return;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kReturn);
}

TEST(Parser, ReturnWithValue) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    return 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kReturn);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(ProceduralStatementParsing, BreakInsideWhile) {
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

TEST(ProceduralStatementParsing, ContinueInsideDoWhile) {
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

TEST(ProceduralStatementParsing, BreakInsideForeach) {
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

TEST(ProceduralStatementParsing, ContinueInsideForeach) {
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

TEST(ProceduralStatementParsing, ReturnFromVoidFunctionEarly) {
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


TEST(ProceduralStatementParsing, ReturnVoid) {
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

TEST(ProceduralStatementParsing, BreakStatementParses) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    forever begin\n"
      "      if (done) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
}

TEST(ProceduralStatementParsing, BreakStatementInBody) {
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

TEST(ProceduralStatementParsing, ContinueStatementParses) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i = i + 1) begin\n"
      "      if (i == 5) continue;\n"
      "      x = i;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  auto* body = stmt->for_body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
}

TEST(ProceduralStatementParsing, ContinueStatementInBody) {
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

}  // namespace
