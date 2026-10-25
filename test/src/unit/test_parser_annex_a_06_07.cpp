#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(CaseSyntaxParsing, UniqueCase) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique case (sel)\n"
      "      1: a = 1;\n"
      "      2: a = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(CaseSyntaxParsing, PriorityCase) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority case (sel)\n"
      "      1: a = 1;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(CaseQualifierParsing, Unique0CaseAtMostOneMatch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 case (sel)\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

TEST(ProceduralStatementParsing, PriorityCasex) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    priority casex (sel)\n"
      "      2'b1?: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(CaseSyntaxParsing, PriorityCasezParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority casez(a)\n"
      "      3'b00?: y = 1;\n"
      "      3'b0??: y = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
}

TEST(CaseKeywordParsing, PlainCaseKindRecorded) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      8'd0: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCase);
  EXPECT_FALSE(stmt->case_inside);
  EXPECT_FALSE(stmt->case_matches);
}

TEST(CaseItemParsing, CommaSeparatedItemExpressions) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      8'd1, 8'd2, 8'd3: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_GE(stmt->case_items.size(), 2u);
  EXPECT_EQ(stmt->case_items[0].patterns.size(), 3u);
  EXPECT_TRUE(stmt->case_items[1].is_default);
}

TEST(CaseItemParsing, DefaultColonOptional) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    case (sel)\n"
              "      8'd0: x = 1;\n"
              "      default x = 0;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

TEST(CaseInsideItemParsing, FlagAndKeywordOnlyOnPlainCase) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel) inside\n"
      "      8'd5: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCase);
  EXPECT_TRUE(stmt->case_inside);
}

TEST(CaseInsideItemParsing, RejectsCasezWithInside) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    casez (sel) inside\n"
      "      8'd5: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  // §12.5 owns the case statement; A.6.7 only states its BNF.
  EXPECT_TRUE(
      ReportedError(r.diags, "'inside' is only valid with 'case'", 3, "12.5"));
}

TEST(CaseInsideItemParsing, RangeListMultipleValueRanges) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel) inside\n"
      "      [8'd1:8'd3], 8'd5, [8'd10:8'd20]: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_inside);
  ASSERT_GE(stmt->case_items.size(), 2u);
  EXPECT_EQ(stmt->case_items[0].patterns.size(), 3u);
}

TEST(ValueRangeParsing, ClosedBracketRange) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    case (sel) inside\n"
              "      [8'd1:8'd9]: x = 1;\n"
              "      default: x = 0;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ValueRangeParsing, OpenLowerBoundDollar) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    case (sel) inside\n"
              "      [$:8'd10]: x = 1;\n"
              "      default: x = 0;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ValueRangeParsing, OpenUpperBoundDollar) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    case (sel) inside\n"
              "      [8'd10:$]: x = 1;\n"
              "      default: x = 0;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ValueRangeParsing, SymmetricTolerancePlusSlashMinus) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    case (sel) inside\n"
              "      [8'd10 +/- 8'd3]: x = 1;\n"
              "      default: x = 0;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ValueRangeParsing, PercentTolerancePlusPercentMinus) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    case (sel) inside\n"
              "      [8'd100 +%- 8'd10]: x = 1;\n"
              "      default: x = 0;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ValueRangeParsing, BareExpressionForm) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel) inside\n"
      "      8'd7: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_inside);
  ASSERT_GE(stmt->case_items.size(), 1u);
  EXPECT_EQ(stmt->case_items[0].patterns.size(), 1u);
}

TEST(CasePatternItemParsing, MatchesFlagSet) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel) matches\n"
      "      8'd0: x = 1;\n"
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

TEST(CasePatternItemParsing, GuardWithAmpAmpAmp) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [7:0] sel;\n"
              "  logic en, x;\n"
              "  initial begin\n"
              "    case (sel) matches\n"
              "      8'd1 &&& en: x = 1'b1;\n"
              "      default: x = 1'b0;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

TEST(CasePatternItemParsing, DefaultColonOptionalUnderMatches) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    case (sel) matches\n"
              "      8'd0: x = 1;\n"
              "      default x = 0;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

TEST(RandcaseStatementParsing, BasicThreeItems) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1: x = 1;\n"
      "      2: x = 2;\n"
      "      3: x = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
  ASSERT_EQ(stmt->randcase_items.size(), 3u);
  EXPECT_NE(stmt->randcase_items[0].first, nullptr);
  EXPECT_NE(stmt->randcase_items[0].second, nullptr);
}

TEST(RandcaseStatementParsing, SingleItem) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
  EXPECT_EQ(stmt->randcase_items.size(), 1u);
}

TEST(RandcaseItemParsing, BodyMayBeNullStatement) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    randcase\n"
              "      1: ;\n"
              "      2: x = 2;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

TEST(RandcaseItemParsing, WeightIsExpression) {
  auto r = Parse(
      "module t;\n"
      "  parameter int W1 = 5;\n"
      "  initial begin\n"
      "    randcase\n"
      "      W1 + 1: x = 1;\n"
      "      (W1 * 2): x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
  ASSERT_EQ(stmt->randcase_items.size(), 2u);
}

TEST(CaseInsideItemParsing, RejectsCasexWithInside) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    casex (sel) inside\n"
      "      8'd1: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  // §12.5 owns the case statement; A.6.7 only states its BNF.
  EXPECT_TRUE(
      ReportedError(r.diags, "'inside' is only valid with 'case'", 3, "12.5"));
}

TEST(CaseInsideItemParsing, RejectsInsideCombinedWithMatches) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel) inside matches\n"
      "      8'd1: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  // §12.5 owns the case statement; A.6.7 only states its BNF.
  EXPECT_TRUE(ReportedError(
      r.diags, "'matches' and 'inside' cannot be used together", 3, "12.5"));
}

TEST(CaseInsideItemParsing, DefaultOnlyItem) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel) inside\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_inside);
  ASSERT_EQ(stmt->case_items.size(), 1u);
  EXPECT_TRUE(stmt->case_items[0].is_default);
}

TEST(CasePatternItemParsing, DefaultOnlyItem) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel) matches\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_matches);
  ASSERT_EQ(stmt->case_items.size(), 1u);
  EXPECT_TRUE(stmt->case_items[0].is_default);
}

TEST(RandcaseItemParsing, RejectsDefaultLabel) {
  // randcase_item ::= expression : statement_or_null
  // — BNF has no default-form alternative, unlike case_item.
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    randcase\n"
      "      default: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  // A randcase_item begins with a weight expression, so `default` reaches
  // ParsePrimaryExpr, whose report is filed under §11.2.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 4, "11.2"));
}

// A.6.7 writes `randcase randcase_item { randcase_item } endcase`, so a
// randcase holds at least one item before its endcase.
TEST(CaseStatementParsing, ARandcaseWithNoItemIsReported) {
  auto r = Parse(
      "module m;\n"
      "  initial randcase endcase\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a randcase statement holds at least one item", 2, "A.6.7"));
  EXPECT_EQ(r.diags.size(), 1u);
}

// A.6.7 writes a pattern-matching case item as a pattern and at most one `&&&`
// filter, an expression, which holds neither another `&&&` nor a `matches`
// (A.8.6). Each is reported; one filter alone is not. A `matches` in
// parentheses is reported once, as one outside a predicate.
TEST(CaseStatementParsing, ACaseItemFilterIsOneExpression) {
  auto r = Parse(
      "module m;\n"
      "  int x, n;\n"
      "  initial case (x) matches\n"
      "    .n &&& n > 0 &&& n < 9: x = 1;\n"
      "    .n &&& n matches 3: x = 2;\n"
      "    .n &&& n > 0: x = 3;\n"
      "    .n &&& (n matches 3): x = 4;\n"
      "  endcase\n"
      "endmodule\n");
  for (uint32_t line : {4u, 5u}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "a pattern-matching case item takes one '&&&' "
                              "filter, which is an expression",
                              line, "A.6.7"))
        << "line " << line;
  }
  EXPECT_TRUE(ReportedError(r.diags,
                            "'matches' and '&&&' stand only in the predicate "
                            "of an if statement or a conditional operator",
                            7, "A.6.6"));
  EXPECT_EQ(r.diags.size(), 3u);
}

// Nor does `matches` follow a case item's pattern, before its filter or not:
// A.6.7.1 ends no pattern with it, and A.8.6 makes it no binary operator.
TEST(CaseStatementParsing, ACaseItemPatternIsNotFollowedByMatches) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial case (x) matches\n"
      "    .n matches 3: x = 1;\n"
      "    .n matches 3 &&& x > 0: x = 2;\n"
      "  endcase\n"
      "endmodule\n");
  for (uint32_t line : {4u, 5u}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "a pattern-matching case item's pattern takes a "
                              "'&&&' filter, not 'matches'",
                              line, "A.6.7"))
        << "line " << line;
  }
  EXPECT_EQ(r.diags.size(), 2u);
}

}  // namespace
