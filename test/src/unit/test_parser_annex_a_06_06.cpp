#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §A.6.6 BNF:
//   conditional_statement ::=
//       [ unique_priority ] if ( cond_predicate ) statement_or_null
//           { else if ( cond_predicate ) statement_or_null }
//           [ else statement_or_null ]

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

// `{ else if ( cond_predicate ) statement_or_null }`: the iteration over
// else-if forms a right-linear chain of nested kIf statements.
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

// statement_or_null permits a null body in either branch.
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

// §A.6.6 BNF:
//   unique_priority ::= unique | unique0 | priority
// Each alternative attaches the corresponding CaseQualifier to the if.

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

// §A.6.6 BNF:
//   cond_predicate ::= expression_or_cond_pattern
//                      { &&& expression_or_cond_pattern }
//   expression_or_cond_pattern ::= expression | cond_pattern

// First alternative of expression_or_cond_pattern: plain expression.
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

// `&&&` repetition is observed as a kBinary node with op == kAmpAmpAmp.
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

// `&&&` may repeat ({ ... } in the BNF). The associativity is irrelevant for
// the syntactic claim; the test only observes that all conjuncts are accepted.
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

// §A.6.6 BNF:
//   cond_pattern ::= expression matches pattern
// Observed via a kBinary node with op == kKwMatches as the if condition.
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

// expression_or_cond_pattern alternation joined by `&&&`: the second conjunct
// is itself a cond_pattern. This exercises the disjunction inside the {…}.
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

// Reverse order: cond_pattern then expression, both joined by `&&&`.
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

// Negative test for the `if ( cond_predicate )` requirement: empty parens
// are not a valid cond_predicate.
TEST(ConditionalStmtBnf, EmptyCondPredicateIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial if () x = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// The `(` after `if` is a literal terminal in the BNF.
TEST(ConditionalStmtBnf, IfMissingLParenIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial if a) x = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// The `)` after cond_predicate is a literal terminal in the BNF.
TEST(ConditionalStmtBnf, IfMissingRParenIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial if (a x = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// The `{ else if ( cond_predicate ) statement_or_null }` element of the BNF
// has no `[ unique_priority ]` slot — only the leading `if` may carry the
// qualifier. A qualifier on a chained else-if violates the BNF.
TEST(ConditionalStmtBnf, UniquePriorityRejectedOnElseIfBranch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique if (a) x = 1;\n"
      "    else unique if (b) x = 2;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// The `{ else if ... }` iteration matched exactly once produces a two-step
// chain: outer if + one else-if + final else.
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

// With nested ifs and a single trailing else, the BNF's greedy structure
// binds the else to the innermost still-open if.
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

// Both expression_or_cond_pattern alternatives on each side of `&&&` may be
// the cond_pattern alternative simultaneously.
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

}  // namespace
