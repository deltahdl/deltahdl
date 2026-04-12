#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ProceduralContinuousAssignmentParsing, ForceVariableAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin force q = 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(ProceduralContinuousAssignmentParsing, ReleaseVariableLvalue) {
  auto r = Parse(
      "module m;\n"
      "  initial begin release q; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
  EXPECT_NE(stmt->lhs, nullptr);
}

TEST(ProceduralContinuousAssignmentParsing, AllSixForms) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assign q = d;\n"
      "    deassign q;\n"
      "    force y = 0;\n"
      "    release y;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto stmts = AllInitialStmts(r);
  ASSERT_EQ(stmts.size(), 4u);
  EXPECT_EQ(stmts[0]->kind, StmtKind::kAssign);
  EXPECT_EQ(stmts[1]->kind, StmtKind::kDeassign);
  EXPECT_EQ(stmts[2]->kind, StmtKind::kForce);
  EXPECT_EQ(stmts[3]->kind, StmtKind::kRelease);
}

TEST(ProceduralContinuousAssignmentParsing, ForceNetAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin force net_a = 0; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
}

TEST(ProceduralContinuousAssignmentParsing, ReleaseNetLvalue) {
  auto r = Parse(
      "module m;\n"
      "  initial begin release net_a; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
}

TEST(ProceduralContinuousAssignmentParsing, ForceWithFuncCallExpressionRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin force a = b + f(c); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

}  // namespace
