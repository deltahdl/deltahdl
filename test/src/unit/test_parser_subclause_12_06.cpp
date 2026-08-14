#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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
  EXPECT_TRUE(r.has_errors);
}

// §12.6 BNF: the `[ pattern ]` after `tagged member_identifier` is optional,
// and §12.6 prose notes that the nested pattern is omitted for void members.
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

TEST(CaseMatchesSyntaxParsing, CaseMatchesEmptyNoItems) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel) matches\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_matches);
  EXPECT_EQ(stmt->case_items.size(), 0u);
}

// Covers the `matches` branch of Parser::TryParseSpecialInfix in
// src/parser/expr_parser.cpp. It assigned no range.start before this commit, so
// a report standing at a cond_pattern printed "<unknown location>" instead of a
// file, line and column. §12.6 writes a cond_pattern as `expression matches
// pattern`, so the node begins where its left operand begins: `x`, at column 15
// of line 2.
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

}  // namespace
