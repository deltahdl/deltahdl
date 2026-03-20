#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ProceduralStatementParsing, NestedIfElse) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a)\n"
      "      if (b) x = 1;\n"
      "      else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);

  EXPECT_EQ(stmt->else_branch, nullptr);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch->else_branch, nullptr);
}

TEST(ProceduralStatementParsing, IfWithBlockBody) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) begin\n"
      "      x = 1;\n"
      "      y = 2;\n"
      "    end else begin\n"
      "      x = 3;\n"
      "      y = 4;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlock);
}

TEST(ProceduralStatementParsing, IfNoElseConditionAndBranches) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->else_branch, nullptr);
}

TEST(ProceduralStatementParsing, IfWithElse) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

TEST(ProceduralStatementParsing, IfBlockBodyThenOnly) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) begin\n"
      "      x = 1;\n"
      "      y = 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
}

TEST(ProceduralStatementParsing, PlainIfHasNoQualifier) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kNone);
}

TEST(AssignmentParsing, NestedIfElseWithExpressions) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] out, a, b;\n"
      "  reg sel1, sel2;\n"
      "  initial begin\n"
      "    if (sel1)\n"
      "      if (sel2)\n"
      "        out = a + b;\n"
      "      else\n"
      "        out = a - b;\n"
      "    else\n"
      "      out = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->then_branch->then_branch->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->then_branch->then_branch->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->then_branch->else_branch->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->then_branch->else_branch->rhs->kind, ExprKind::kBinary);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlockingAssign);
}

TEST(ProceduralStatementParsing, BasicIfElse) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  ASSERT_NE(stmt->then_branch, nullptr);
  ASSERT_NE(stmt->else_branch, nullptr);
}

TEST(ProceduralStatementParsing, IfWithoutElse) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->else_branch, nullptr);
}

TEST(ProcessParsing, IfElse) {
  auto r = Parse(
      "module m;\n"
      "  logic sel, a, b, y;\n"
      "  always_comb begin\n"
      "    if (sel)\n"
      "      y = a;\n"
      "    else\n"
      "      y = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

TEST(ProcessParsing, BlockWithIfElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (sel)\n"
      "      a = 1;\n"
      "    else\n"
      "      a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

TEST(AssignmentParsing, InIfElseBranches) {
  auto r = Parse(
      "module m;\n"
      "  reg a, sel;\n"
      "  initial begin\n"
      "    if (sel)\n"
      "      a = 1;\n"
      "    else\n"
      "      a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlockingAssign);
}

}  // namespace
