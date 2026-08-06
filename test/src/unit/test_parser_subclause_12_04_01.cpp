#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

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
