#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt *FirstInitialStmt(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock)
      continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

} // namespace

// =============================================================================
// A.6.6 Conditional statements
// =============================================================================

// ---------------------------------------------------------------------------
// conditional_statement ::=
//   [ unique_priority ] if ( cond_predicate ) statement_or_null
//   { else if ( cond_predicate ) statement_or_null }
//   [ else statement_or_null ]
// ---------------------------------------------------------------------------

// §12.4: basic if statement — true branch only, no else
TEST(ParserA606, IfOnly) {
  auto r = Parse("module m;\n"
                 "  initial begin if (a) x = 1; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->else_branch, nullptr);
}

// §12.4: if-else statement
TEST(ParserA606, IfElse) {
  auto r = Parse("module m;\n"
                 "  initial begin if (a) x = 1; else x = 0; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlockingAssign);
}

// §12.4.1: if-else-if chain with final else
TEST(ParserA606, IfElseIfElse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    if (a) x = 1;\n"
                 "    else if (b) x = 2;\n"
                 "    else x = 3;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // else branch is another if statement
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  // the inner if has its own else
  ASSERT_NE(stmt->else_branch->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->else_branch->kind, StmtKind::kBlockingAssign);
}

// §12.4.1: multi-way if-else-if chain without final else
TEST(ParserA606, IfElseIfNoFinalElse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    if (a) x = 1;\n"
                 "    else if (b) x = 2;\n"
                 "    else if (c) x = 3;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->else_branch->kind, StmtKind::kIf);
  // last else-if has no else
  EXPECT_EQ(stmt->else_branch->else_branch->else_branch, nullptr);
}

// §12.4: if with null statement_or_null (semicolon) for then branch
TEST(ParserA606, IfNullThen) {
  auto r = Parse("module m;\n"
                 "  initial begin if (a) ; else x = 0; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kNull);
  ASSERT_NE(stmt->else_branch, nullptr);
}

// §12.4: if with null else branch
TEST(ParserA606, IfNullElse) {
  auto r = Parse("module m;\n"
                 "  initial begin if (a) x = 1; else ; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kNull);
}

// §12.4: if with begin-end block in both branches
TEST(ParserA606, IfElseWithBlocks) {
  auto r = Parse("module m;\n"
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
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlock);
}

// §12.4: dangling else associates with closest if
TEST(ParserA606, DanglingElse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    if (a)\n"
                 "      if (b) x = 1;\n"
                 "      else x = 2;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // outer if has no else — the else belongs to the inner if
  EXPECT_EQ(stmt->else_branch, nullptr);
  // then_branch is the inner if, which has an else
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch->else_branch, nullptr);
}

// §12.4: forced else association with begin-end
TEST(ParserA606, ForcedElseWithBeginEnd) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    if (a) begin\n"
                 "      if (b) x = 1;\n"
                 "    end\n"
                 "    else x = 2;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // outer if now has else (because begin-end blocks inner if)
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlockingAssign);
  // then_branch is a block containing inner if with no else
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
}

// ---------------------------------------------------------------------------
// unique_priority ::= unique | unique0 | priority
// ---------------------------------------------------------------------------

// §12.4.2: unique if
TEST(ParserA606, UniqueIf) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    unique if (a == 0) x = 1;\n"
                 "    else if (a == 1) x = 2;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

// §12.4.2: unique0 if
TEST(ParserA606, Unique0If) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    unique0 if (a == 0) x = 1;\n"
                 "    else if (a == 1) x = 2;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

// §12.4.2: priority if
TEST(ParserA606, PriorityIf) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    priority if (a == 0) x = 1;\n"
                 "    else if (a == 1) x = 2;\n"
                 "    else x = 3;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

// §12.4.2: unique if with else-if chain and final else
TEST(ParserA606, UniqueIfElseIfElse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    unique if (a == 0) x = 1;\n"
                 "    else if (a == 1) x = 2;\n"
                 "    else if (a == 2) x = 3;\n"
                 "    else x = 4;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
  // qualifier only on outermost if; else-if branches are plain if stmts
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->else_branch->qualifier, CaseQualifier::kNone);
}

// ---------------------------------------------------------------------------
// cond_predicate ::=
//   expression_or_cond_pattern { &&& expression_or_cond_pattern }
// ---------------------------------------------------------------------------

// §12.6: cond_predicate with &&& operator
TEST(ParserA606, CondPredicateTripleAnd) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    if (a &&& b) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
}

// ---------------------------------------------------------------------------
// expression_or_cond_pattern ::= expression | cond_pattern
// cond_pattern ::= expression matches pattern
// ---------------------------------------------------------------------------

// §12.6: cond_pattern in if condition — expr matches constant
TEST(ParserA606, CondPatternMatchesConstant) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    if (x matches 3) y = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // condition should be a matches binary expression
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->condition->op, TokenKind::kKwMatches);
}

// §12.6: matches with &&& in cond_predicate
TEST(ParserA606, CondPatternMatchesWithTripleAnd) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    if (x matches 5 &&& en) y = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
}

// ---------------------------------------------------------------------------
// Structural tests: nested conditionals, complex conditions
// ---------------------------------------------------------------------------

// §12.4: nested if inside begin-end
TEST(ParserA606, NestedIfInBlock) {
  auto r = Parse("module m;\n"
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
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // both branches are blocks
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlock);
}

// §12.4: complex condition expression
TEST(ParserA606, ComplexCondExpression) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    if ((a > 0) && (b < 10) || c) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
}

// §12.4: if condition with function call
TEST(ParserA606, IfCondFunctionCall) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    if ($unsigned(a) > 0) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
}
