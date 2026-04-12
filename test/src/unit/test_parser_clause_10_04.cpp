#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

static ModuleItem* FindInitialBlock(ParseResult& r) {
  return FindItemByKind(r, ModuleItemKind::kInitialBlock);
}

TEST(ProceduralAssignmentParsing, MixBlockingNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c, d;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    c <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* init_item = FindInitialBlock(r);
  ASSERT_NE(init_item, nullptr);
  auto* body = init_item->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNonblockingAssign);
}

TEST(ProceduralAssignmentParsing, BlockingAssignInAlways) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  always @(b) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(item->body->lhs, nullptr);
  EXPECT_NE(item->body->rhs, nullptr);
}

TEST(ProceduralAssignmentParsing, InTaskBody) {
  auto r = Parse(
      "module m;\n"
      "  task t();\n"
      "    int x;\n"
      "    x = 42;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* task = FindItemByKind(r, ModuleItemKind::kTaskDecl);
  ASSERT_NE(task, nullptr);
  ASSERT_NE(task->body, nullptr);
  ASSERT_GE(task->body->stmts.size(), 1u);
  auto* assign = task->body->stmts.back();
  EXPECT_EQ(assign->kind, StmtKind::kBlockingAssign);
}

TEST(ProceduralAssignmentParsing, InFunctionBody) {
  auto r = Parse(
      "module m;\n"
      "  function int compute(int a, int b);\n"
      "    int tmp;\n"
      "    tmp = a + b;\n"
      "    return tmp;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_NE(func->body, nullptr);
  auto* assign = FindStmtByKind(func->body->stmts, StmtKind::kBlockingAssign);
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(assign->lhs->text, "tmp");
}

TEST(ProceduralAssignmentParsing, InInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg a;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* init_item = FindInitialBlock(r);
  ASSERT_NE(init_item, nullptr);
  auto* body = init_item->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
}

TEST(ProceduralAssignmentParsing, AllThreeAssignmentTypes) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b <= 2;\n"
      "    c += 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto stmts = AllInitialStmts(r);
  ASSERT_EQ(stmts.size(), 3u);
  EXPECT_EQ(stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmts[1]->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmts[2]->kind, StmtKind::kBlockingAssign);
}

}  // namespace
