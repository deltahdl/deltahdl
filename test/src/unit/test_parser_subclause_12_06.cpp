#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(CaseMatchesSyntaxParsing, PatternParenthesized) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (e matches (tagged Valid .n)) x = n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CaseMatchesSyntaxParsing, CaseMatchesKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel) matches\n"
      "      8'd5: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_TRUE(stmt->case_matches);
  EXPECT_FALSE(stmt->case_inside);
}

TEST(CaseMatchesSyntaxParsing, CaseMatchesWithGuard) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel) matches\n"
      "      8'd5 &&& guard: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_matches);
  ASSERT_GE(stmt->case_items.size(), 1u);
  auto* pat = stmt->case_items[0].patterns[0];
  EXPECT_EQ(pat->kind, ExprKind::kBinary);
  EXPECT_EQ(pat->op, TokenKind::kAmpAmpAmp);
}

TEST(CaseMatchesSyntaxParsing, CasezMatches) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    casez (sel) matches\n"
      "      4'b1???: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_matches);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
}

TEST(CaseMatchesSyntaxParsing, CasexMatches) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    casex (sel) matches\n"
      "      4'b1???: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_matches);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
}

TEST(CaseMatchesSyntaxParsing, CaseInsideAndMatchesMutualExclusion) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel) inside matches\n"
      "      8'd5: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "'matches' and 'inside' cannot be used together", 3, "12.5"));
}

TEST(CaseMatchesSyntaxParsing, TaggedVoidMemberOmitsNestedPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (e matches tagged Invalid) x = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CaseMatchesSyntaxParsing, CaseMatchesWithNoItemsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel) matches\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "case statement shall have at least one case item", 4, "12.5"));
}

TEST(CaseMatchesSyntaxParsing, MatchesCondPatternStartsAtItsLeftOperand) {
  auto r = Parse(
      "module m;\n"
      "  initial if (x matches 8'd5) y = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->op, TokenKind::kKwMatches);
  EXPECT_EQ(stmt->condition->range.start.line, 2u);
  EXPECT_EQ(stmt->condition->range.start.column, 15u);
}

TEST(PatternSyntaxParsing, TaggedMemberPatternStopsAtFilterAndQuestion) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (v matches tagged Valid .* &&& flag) x = 1;\n"
      "    x = v matches tagged Invalid ? 10 : 20;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 2u);
  const Expr* cond = body->stmts[0]->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->op, TokenKind::kAmpAmpAmp);
  ASSERT_NE(cond->lhs, nullptr);
  EXPECT_EQ(cond->lhs->op, TokenKind::kKwMatches);
  ASSERT_NE(cond->lhs->rhs, nullptr);
  EXPECT_EQ(cond->lhs->rhs->kind, ExprKind::kTagged);
  ASSERT_NE(cond->lhs->rhs->lhs, nullptr);
  EXPECT_EQ(cond->lhs->rhs->lhs->text, ".*");
  const Expr* rhs = body->stmts[1]->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->op, TokenKind::kKwMatches);
  ASSERT_NE(rhs->condition->rhs, nullptr);
  EXPECT_EQ(rhs->condition->rhs->lhs, nullptr);
}

}  // namespace
