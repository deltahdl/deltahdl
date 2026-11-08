#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;
namespace {

TEST(LoopStatementSyntax, SixLoopAlternatives) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    forever break;\n"
      "    repeat (3) x = 1;\n"
      "    while (c) x = 2;\n"
      "    for (int i = 0; i < 3; i++) x = 3;\n"
      "    do x = 4; while (c);\n"
      "    foreach (arr[j]) x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto stmts = AllInitialStmts(r);
  ASSERT_EQ(stmts.size(), 6u);
  EXPECT_EQ(stmts[0]->kind, StmtKind::kForever);
  EXPECT_EQ(stmts[1]->kind, StmtKind::kRepeat);
  EXPECT_EQ(stmts[2]->kind, StmtKind::kWhile);
  EXPECT_EQ(stmts[3]->kind, StmtKind::kFor);
  EXPECT_EQ(stmts[4]->kind, StmtKind::kDoWhile);
  EXPECT_EQ(stmts[5]->kind, StmtKind::kForeach);
}

TEST(LoopStatementSyntax, ForInitializationAssignmentsForm) {
  auto r = Parse(
      "module m;\n"
      "  integer i, j;\n"
      "  initial\n"
      "    for (i = 0, j = 10; i < j; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_EQ(stmt->for_inits.size(), 2u);
  EXPECT_EQ(stmt->for_inits[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->for_inits[1]->kind, StmtKind::kBlockingAssign);
  ASSERT_EQ(stmt->for_init_types.size(), 2u);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kImplicit);
  EXPECT_EQ(stmt->for_init_types[1].kind, DataTypeKind::kImplicit);
}

TEST(LoopStatementSyntax, ForInitializationDeclarationForm) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (int i = 0; i < 3; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->for_init_types.size(), 1u);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kInt);
  ASSERT_EQ(stmt->for_inits.size(), 1u);
  EXPECT_EQ(stmt->for_inits[0]->kind, StmtKind::kBlockingAssign);
}

TEST(LoopStatementSyntax, ForInitializationMultipleDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (int i = 0, int j = 4; i < j; i++, j--) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_EQ(stmt->for_inits.size(), 2u);
  ASSERT_EQ(stmt->for_init_types.size(), 2u);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kInt);
  EXPECT_EQ(stmt->for_init_types[1].kind, DataTypeKind::kInt);
}

TEST(LoopStatementSyntax, ForVariableDeclarationVarKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (var int i = 0; i < 3; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->for_init_types.size(), 1u);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kInt);
}

TEST(LoopStatementSyntax, ForVariableDeclarationContinuationForm) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (int i = 0, j = i + 3; i < j; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_EQ(stmt->for_inits.size(), 2u);
  EXPECT_EQ(stmt->for_inits[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->for_inits[1]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kInt);
}

TEST(LoopStatementSyntax, ForStepThreeAlternatives) {
  auto r = Parse(
      "module m;\n"
      "  function void step(); endfunction\n"
      "  initial\n"
      "    for (i = 0; i < 3; i += 1, i++, step()) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->for_steps.size(), 3u);
  EXPECT_EQ(stmt->for_steps[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->for_steps[1]->kind, StmtKind::kExprStmt);
  EXPECT_EQ(stmt->for_steps[2]->kind, StmtKind::kExprStmt);
  EXPECT_EQ(stmt->for_steps[2]->expr->kind, ExprKind::kCall);
}

TEST(LoopStatementSyntax, LoopVariablesOmittedSlot) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    foreach (arr[, j]) x = j;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_TRUE(stmt->foreach_vars[0].empty());
  EXPECT_EQ(stmt->foreach_vars[1], "j");
}

TEST(LoopStatementSyntax, LoopVariablesAllNamed) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    foreach (m[i, j]) x = i + j;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
  EXPECT_EQ(stmt->foreach_vars[1], "j");
}

TEST(LoopStatementSyntax, LoopVariablesTrailingOmitted) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    foreach (arr[i, ]) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
  EXPECT_TRUE(stmt->foreach_vars[1].empty());
}

TEST(LoopStatementSyntax, ForInitializationClauseOmitted) {
  auto r = Parse(
      "module m;\n"
      "  integer i;\n"
      "  initial\n"
      "    for (; i < 3; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_TRUE(stmt->for_inits.empty());
  EXPECT_NE(stmt->for_cond, nullptr);
  ASSERT_EQ(stmt->for_steps.size(), 1u);
}

TEST(LoopStatementSyntax, ForConditionClauseOmitted) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (int i = 0;; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_EQ(stmt->for_inits.size(), 1u);
  EXPECT_EQ(stmt->for_cond, nullptr);
}

TEST(LoopStatementSyntax, ForStepClauseOmitted) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (int i = 0; i < 3;) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_TRUE(stmt->for_steps.empty());
}

TEST(LoopStatementSyntax, ForAllClausesOmitted) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (;;) x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_TRUE(stmt->for_inits.empty());
  EXPECT_EQ(stmt->for_cond, nullptr);
  EXPECT_TRUE(stmt->for_steps.empty());
}

TEST(LoopStatementSyntax, LoopBodyNullStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    while (c) ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kNull);
}

TEST(LoopStatementSyntax, ForVariableDeclarationVectorType) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (logic [7:0] i = 0; i < 8; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->for_init_types.size(), 1u);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kLogic);
}

TEST(LoopStatementSyntax, ForVariableDeclarationBitType) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (bit i = 0; i < 1; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->for_init_types.size(), 1u);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kBit);
}

TEST(LoopStatementSyntax, ForVariableDeclarationNamedType) {
  auto r = Parse(
      "module m;\n"
      "  typedef int my_t;\n"
      "  initial\n"
      "    for (my_t i = 0; i < 3; i++) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_EQ(stmt->for_init_types.size(), 1u);
  EXPECT_EQ(stmt->for_init_types[0].kind, DataTypeKind::kNamed);
  EXPECT_EQ(stmt->for_init_types[0].type_name, "my_t");
  ASSERT_EQ(stmt->for_inits.size(), 1u);
  EXPECT_EQ(stmt->for_inits[0]->kind, StmtKind::kBlockingAssign);
}

TEST(LoopStatementSyntax, RepeatRequiresParenthesizedExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    repeat 3 x = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got integer literal", 3, "12.7.2"));
}

TEST(LoopStatementSyntax, WhileRequiresParenthesizedExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    while c x = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got identifier", 3, "12.7.4"));
}

TEST(LoopStatementSyntax, ForeachRequiresParentheses) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    foreach arr[i] x = i;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got identifier", 3, "12.7.3"));
}

TEST(LoopStatementSyntax, ForRequiresClauseSemicolons) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    for (int i = 0 i < 3; i++) x = i;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got identifier", 3, "12.7.1"));
}

TEST(LoopStatementSyntax, DoWhileRequiresWhileKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    do x = 1; y = 2;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'while', got identifier", 3, "12.7.5"));
}

}  // namespace
