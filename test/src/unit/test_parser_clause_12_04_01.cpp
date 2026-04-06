#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(IfElseIfParsing, IfElseIfChain) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else if (c) x = 3;\n"
      "    else x = 4;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->else_branch->kind, StmtKind::kIf);
}

TEST(ConditionalSyntaxParsing, IfElseIfElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else x = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);

  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);

  ASSERT_NE(stmt->else_branch->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->else_branch->kind, StmtKind::kBlockingAssign);
}

TEST(ConditionalSyntaxParsing, IfElseIfNoFinalElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else if (c) x = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->else_branch->kind, StmtKind::kIf);

  EXPECT_EQ(stmt->else_branch->else_branch->else_branch, nullptr);
}

TEST(IfElseIfParsing, IfElseIfElseChain) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a == 0) x = 0;\n"
      "    else if (a == 1) x = 1;\n"
      "    else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  EXPECT_NE(stmt->else_branch->else_branch, nullptr);
}
static ModuleItem* FirstAlwaysLatchItem(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) return item;
  }
  return nullptr;
}

TEST(IfElseIfParsing, IfElseIfInAlwaysLatch) {
  auto r = Parse(
      "module m;\n"
      "  logic en1, en2, d1, d2, q;\n"
      "  always_latch\n"
      "    if (en1)\n"
      "      q <= d1;\n"
      "    else if (en2)\n"
      "      q <= d2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);

  ASSERT_NE(item->body->else_branch, nullptr);
  EXPECT_EQ(item->body->else_branch->kind, StmtKind::kIf);
}

TEST(ConditionalSyntaxParsing, DeepIfElseIfChain) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) x = 0;\n"
      "    else if (b) x = 1;\n"
      "    else if (c) x = 2;\n"
      "    else if (d) x = 3;\n"
      "    else x = 4;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // Walk the chain: 4 levels of if
  auto* s1 = stmt->else_branch;
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s1->kind, StmtKind::kIf);
  auto* s2 = s1->else_branch;
  ASSERT_NE(s2, nullptr);
  EXPECT_EQ(s2->kind, StmtKind::kIf);
  auto* s3 = s2->else_branch;
  ASSERT_NE(s3, nullptr);
  EXPECT_EQ(s3->kind, StmtKind::kIf);
  ASSERT_NE(s3->else_branch, nullptr);
  EXPECT_EQ(s3->else_branch->kind, StmtKind::kBlockingAssign);
}

TEST(IfElseIfParsing, IfElseIfWithBlockBodies) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) begin\n"
      "      x = 1;\n"
      "      y = 2;\n"
      "    end else if (b) begin\n"
      "      x = 3;\n"
      "      y = 4;\n"
      "    end else begin\n"
      "      x = 5;\n"
      "      y = 6;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->else_branch->then_branch->kind, StmtKind::kBlock);
  ASSERT_NE(stmt->else_branch->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->else_branch->kind, StmtKind::kBlock);
}

}  // namespace
