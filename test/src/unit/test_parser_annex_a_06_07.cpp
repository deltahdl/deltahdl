#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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
  EXPECT_TRUE(r.has_errors);
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
  EXPECT_TRUE(r.has_errors);
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
  EXPECT_TRUE(r.has_errors);
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
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
