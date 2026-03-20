#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ConditionalSyntaxParsing, IfBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) b = 1;\n"
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
}

TEST(ConditionalSyntaxParsing, IfOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin if (a) x = 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->else_branch, nullptr);
}

TEST(ConditionalSyntaxParsing, IfElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin if (a) x = 1; else x = 0; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlockingAssign);
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
  EXPECT_NE(stmt->else_branch->else_branch, nullptr);
}

TEST(ConditionalSyntaxParsing, UniqueIf) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique if (a) x = 1;\n"
      "    else x = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(ConditionalSyntaxParsing, Unique0If) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 if (a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

TEST(ConditionalSyntaxParsing, PriorityIf) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else x = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(ConditionalSyntaxParsing, IfNullThenBranch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) ;\n"
      "    else b = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kNull);
  EXPECT_NE(stmt->else_branch, nullptr);
}

TEST(ConditionalSyntaxParsing, IfNullThen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin if (a) ; else x = 0; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kNull);
  ASSERT_NE(stmt->else_branch, nullptr);
}

TEST(ConditionalSyntaxParsing, IfNullElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin if (a) x = 1; else ; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kNull);
}

TEST(ConditionalSyntaxParsing, IfWithBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) begin\n"
      "      x = 1;\n"
      "      y = 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
}

TEST(ConditionalSyntaxParsing, IfElseWithBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (cond) begin\n"
      "      x = 1;\n"
      "      y = 2;\n"
      "    end else begin\n"
      "      x = 3;\n"
      "      y = 4;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlock);
}

TEST(ConditionalSyntaxParsing, DanglingElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a)\n"
      "      if (b) x = 1;\n"
      "      else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);

  EXPECT_EQ(stmt->else_branch, nullptr);

  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch->else_branch, nullptr);
}

TEST(ConditionalSyntaxParsing, ForcedElseWithBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) begin\n"
      "      if (b) x = 1;\n"
      "    end\n"
      "    else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);

  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlockingAssign);

  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
}

TEST(ConditionalSyntaxParsing, NestedIfInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) begin\n"
      "      if (b) x = 1;\n"
      "      else x = 2;\n"
      "    end else begin\n"
      "      if (c) x = 3;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);

  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlock);
}

TEST(ConditionalSyntaxParsing, ComplexCondExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if ((a > 0) && (b < 10) || c) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
}

TEST(ConditionalSyntaxParsing, IfCondFunctionCall) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if ($unsigned(a) > 0) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
}

TEST(ConditionalSyntaxParsing, UniqueIfElseIfElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique if (a == 0) x = 1;\n"
      "    else if (a == 1) x = 2;\n"
      "    else if (a == 2) x = 3;\n"
      "    else x = 4;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);

  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->else_branch->qualifier, CaseQualifier::kNone);
}

TEST(ConditionalQualifierParsing, UniqueIf) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else x = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(ConditionalQualifierParsing, Unique0If) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

TEST(ConditionalQualifierParsing, PriorityIf) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else x = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(ConditionalSyntaxParsing, CondPredicateTripleAnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a &&& b) x = 1;\n"
      "  end\n"
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

TEST(ConditionalSyntaxParsing, CondPredicateChainedTripleAnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a &&& b &&& c) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
}

TEST(ConditionalSyntaxParsing, CondPatternMatchesConstant) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 3) y = 1;\n"
      "  end\n"
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

TEST(ConditionalSyntaxParsing, CondPatternMatchesWithTripleAnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 5 &&& en) y = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
}

TEST(PatternParsing, MatchesExprInIfCondition) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 5) y = 1;\n"
      "  end\n"
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

TEST(PatternParsing, MatchesWithTripleAndInIf) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 5 &&& en) y = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, CondPatternMatches) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 42) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConditionalSyntaxParsing, IfMissingOpenParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConditionalSyntaxParsing, IfMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a x = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConditionalSyntaxParsing, IfEmptyCondition) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if () x = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConditionalSyntaxParsing, IfNonblockingAssignBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) x <= 1;\n"
      "    else x <= 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kNonblockingAssign);
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

TEST(ConditionalSyntaxParsing, PriorityIfNoElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->else_branch->else_branch, nullptr);
}

TEST(ConditionalSyntaxParsing, Unique0IfWithElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else x = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  EXPECT_NE(stmt->else_branch->else_branch, nullptr);
}

TEST(ConditionalSyntaxParsing, NestedQualifiedIfs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority if (a) begin\n"
      "      unique if (b) x = 1;\n"
      "      else x = 2;\n"
      "    end else begin\n"
      "      x = 3;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* outer = FirstInitialStmt(r);
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(outer->qualifier, CaseQualifier::kPriority);
  ASSERT_NE(outer->then_branch, nullptr);
  EXPECT_EQ(outer->then_branch->kind, StmtKind::kBlock);
  auto* inner = outer->then_branch->stmts[0];
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(inner->qualifier, CaseQualifier::kUnique);
}

TEST(ConditionalSyntaxParsing, CondPredicateExprThenMatches) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (en &&& x matches 5) y = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
}

TEST(ConditionalSyntaxParsing, IfSubroutineCallBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) $display(\"true\");\n"
      "    else $display(\"false\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

TEST(ConditionalSyntaxParsing, PlainIfNoQualifier) {
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
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kNone);
}

}  // namespace
