#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(AssignmentOverviewParsing, BlockingAssignStructure) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    x = y;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(AssignmentOverviewParsing, NonblockingAssignStructure) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    x <= y;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(AssignmentOverviewParsing, ContinuousAssignStructure) {
  auto r = Parse(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  EXPECT_EQ(ca->kind, ModuleItemKind::kContAssign);
  EXPECT_NE(ca->assign_lhs, nullptr);
  EXPECT_NE(ca->assign_rhs, nullptr);
}

TEST(AssignmentOverviewParsing, ContAssignConcatenationLhs) {
  auto r = Parse(
      "module t;\n"
      "  wire a, b;\n"
      "  assign {a, b} = 2'b10;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kConcatenation);
}

TEST(AssignmentOverviewParsing, ContAssignNestedConcatenationLhs) {
  auto r = Parse(
      "module t;\n"
      "  wire a, b, c, d;\n"
      "  assign {{a, b}, {c, d}} = 4'b1010;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kConcatenation);
  ASSERT_GE(ca->assign_lhs->elements.size(), 2u);
  EXPECT_EQ(ca->assign_lhs->elements[0]->kind, ExprKind::kConcatenation);
  EXPECT_EQ(ca->assign_lhs->elements[1]->kind, ExprKind::kConcatenation);
}

TEST(AssignmentOverviewParsing, ContAssignConstBitSelectLhs) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  assign w[3] = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kSelect);
}

TEST(AssignmentOverviewParsing, ContAssignConstPartSelectLhs) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  assign w[3:0] = 4'b1010;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kSelect);
}

TEST(AssignmentOverviewParsing, ProceduralBitSelectLhs) {
  auto r = Parse(
      "module t;\n"
      "  initial v[3] = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(AssignmentOverviewParsing, ProceduralPartSelectLhs) {
  auto r = Parse(
      "module t;\n"
      "  initial v[7:0] = 8'hAB;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(AssignmentOverviewParsing, ProceduralMemoryWordLhs) {
  auto r = Parse(
      "module t;\n"
      "  initial mem[2] = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(AssignmentOverviewParsing, ProceduralConcatenationLhs) {
  auto r = Parse(
      "module t;\n"
      "  initial {a, b} = 2'b10;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

TEST(AssignmentOverviewParsing, ProceduralNestedConcatenationLhs) {
  auto r = Parse(
      "module t;\n"
      "  initial {{a, b}, {c, d}} = 4'b1100;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  ASSERT_GE(stmt->lhs->elements.size(), 2u);
  EXPECT_EQ(stmt->lhs->elements[0]->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements[1]->kind, ExprKind::kConcatenation);
}

TEST(AssignmentOverviewParsing, RhsComplexExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a + b) * c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

}  // namespace
