#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(ConditionalStmtBnf, IfThenOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kNone);
}

TEST(ConditionalStmtBnf, IfThenElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) x = 1; else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  ASSERT_NE(stmt->else_branch, nullptr);
}

TEST(ConditionalStmtBnf, ElseIfChainNests) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else if (c) x = 3;\n"
      "    else x = 4;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* outer = FirstInitialStmt(r);
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(outer->kind, StmtKind::kIf);
  ASSERT_NE(outer->else_branch, nullptr);
  EXPECT_EQ(outer->else_branch->kind, StmtKind::kIf);
  ASSERT_NE(outer->else_branch->else_branch, nullptr);
  EXPECT_EQ(outer->else_branch->else_branch->kind, StmtKind::kIf);
  ASSERT_NE(outer->else_branch->else_branch->else_branch, nullptr);
}

TEST(ConditionalStmtBnf, ThenBranchIsNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kNull);
}

TEST(ConditionalStmtBnf, ElseBranchIsNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) x = 1; else ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kNull);
}

TEST(ConditionalStmtBnf, UniquePriorityUnique) {
  auto r = Parse(
      "module m;\n"
      "  initial unique if (a) x = 1; else x = 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(ConditionalStmtBnf, UniquePriorityUnique0) {
  auto r = Parse(
      "module m;\n"
      "  initial unique0 if (a) x = 1; else x = 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

TEST(ConditionalStmtBnf, UniquePriorityPriority) {
  auto r = Parse(
      "module m;\n"
      "  initial priority if (a) x = 1; else x = 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(ConditionalStmtBnf, CondPredicateBareExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial if (a + 1) x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
}

TEST(ConditionalStmtBnf, CondPredicateTripleAmpJoinsTwoExpressions) {
  auto r = Parse(
      "module m;\n"
      "  initial if (a &&& b) x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->condition->op, TokenKind::kAmpAmpAmp);
}

TEST(ConditionalStmtBnf, CondPredicateTripleAmpRepeats) {
  auto r = Parse(
      "module m;\n"
      "  initial if (a &&& b &&& c) x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->condition->op, TokenKind::kAmpAmpAmp);
}

TEST(ConditionalStmtBnf, CondPatternMatchesPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial if (x matches 3) y = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->condition->op, TokenKind::kKwMatches);
}

TEST(ConditionalStmtBnf, CondPredicateExpressionAmpAmpAmpCondPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial if (en &&& x matches 5) y = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->condition->op, TokenKind::kAmpAmpAmp);
}

TEST(ConditionalStmtBnf, CondPredicateCondPatternAmpAmpAmpExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial if (x matches 5 &&& en) y = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
}

TEST(ConditionalStmtBnf, EmptyCondPredicateIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial if () x = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

TEST(ConditionalStmtBnf, IfMissingLParenIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial if a) x = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got identifier", 2, "12.4"));
}

TEST(ConditionalStmtBnf, IfMissingRParenIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial if (a x = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ')', got identifier", 2, "12.4"));
}

TEST(ConditionalStmtBnf, UniquePriorityRejectedOnElseIfBranch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique if (a) x = 1;\n"
      "    else unique if (b) x = 2;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "unique, unique0, or priority cannot appear on an else-if branch", 4,
      "12.4.2"));
}

TEST(ConditionalStmtBnf, SingleElseIfBranch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* outer = FirstInitialStmt(r);
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(outer->kind, StmtKind::kIf);
  ASSERT_NE(outer->else_branch, nullptr);
  EXPECT_EQ(outer->else_branch->kind, StmtKind::kIf);
  EXPECT_EQ(outer->else_branch->else_branch, nullptr);
}

TEST(ConditionalStmtBnf, DanglingElseBindsToInnermostIf) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) if (b) x = 1; else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* outer = FirstInitialStmt(r);
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(outer->kind, StmtKind::kIf);
  ASSERT_NE(outer->then_branch, nullptr);
  EXPECT_EQ(outer->then_branch->kind, StmtKind::kIf);
  EXPECT_NE(outer->then_branch->else_branch, nullptr);
  EXPECT_EQ(outer->else_branch, nullptr);
}

TEST(ConditionalStmtBnf, CondPredicateTwoCondPatternsAroundTripleAmp) {
  auto r = Parse(
      "module m;\n"
      "  initial if (x matches 1 &&& y matches 2) z = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->condition->op, TokenKind::kAmpAmpAmp);
  ASSERT_NE(stmt->condition->lhs, nullptr);
  EXPECT_EQ(stmt->condition->lhs->op, TokenKind::kKwMatches);
  ASSERT_NE(stmt->condition->rhs, nullptr);
  EXPECT_EQ(stmt->condition->rhs->op, TokenKind::kKwMatches);
}

TEST(ConditionalStmtBnf, CondPredicateTripleAmpStartsAtItsLeftOperand) {
  auto r = Parse(
      "module m;\n"
      "  initial if (a &&& b) x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->op, TokenKind::kAmpAmpAmp);
  EXPECT_EQ(stmt->condition->range.start.line, 2u);
  EXPECT_EQ(stmt->condition->range.start.column, 15u);
}

TEST(ConditionalStmtBnf, AConditionalOperatorTakesTheWholeTripleAmpPredicate) {
  auto r = Parse(
      "module m;\n"
      "  int x, y, z;\n"
      "  initial z = x matches 5 &&& y > 0 ? 1 : 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  ASSERT_EQ(stmt->rhs->kind, ExprKind::kTernary);
  ASSERT_NE(stmt->rhs->condition, nullptr);
  EXPECT_EQ(stmt->rhs->condition->op, TokenKind::kAmpAmpAmp);
  ASSERT_NE(stmt->rhs->condition->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->condition->rhs->op, TokenKind::kGt);
}

TEST(ConditionalStmtBnf, AMatchesClauseTakesAnImplicationWhole) {
  auto r = Parse(
      "module m;\n"
      "  int b, c;\n"
      "  initial if (b -> c matches 3) b = 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->op, TokenKind::kKwMatches);
  ASSERT_NE(stmt->condition->lhs, nullptr);
  EXPECT_EQ(stmt->condition->lhs->op, TokenKind::kArrow);
}

TEST(ConditionalStmtBnf, APredicateOutsideAConditionIsReported) {
  auto r = Parse(
      "module m;\n"
      "  int x, y;\n"
      "  logic b;\n"
      "  initial begin\n"
      "    b = x matches 5;\n"
      "    b = x &&& y;\n"
      "    while (x matches 5) x++;\n"
      "    if ((x matches 5)) y = 1;\n"
      "    y = (x matches 5) ? 1 : 0;\n"
      "    y = b ? x matches 5 : 0;\n"
      "  end\n"
      "endmodule\n");
  for (uint32_t line : {5u, 6u, 7u, 8u, 9u, 10u}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "'matches' and '&&&' stand only in the predicate "
                              "of an if statement or a conditional operator",
                              line, "A.6.6"))
        << "line " << line;
  }
  EXPECT_EQ(r.diags.size(), 6u);
}

TEST(ConditionalStmtBnf, APredicateInAConditionIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  int x, y;\n"
      "  initial begin\n"
      "    if (x matches 5) y = 1;\n"
      "    if (x matches 5 &&& y > 0) y = 1;\n"
      "    else if (y matches 2) y = 2;\n"
      "    y = x matches 5 ? 1 : 0;\n"
      "    y = x matches 5 &&& y > 0 ? 1 : 0;\n"
      "    case (x) matches\n"
      "      .n &&& n > 0: y = n;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
