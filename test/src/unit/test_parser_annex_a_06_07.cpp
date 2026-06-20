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

static ModuleItem* FirstAlwaysLatchItem(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) return item;
  }
  return nullptr;
}

TEST(CaseQualifierParsing, UniqueCaseOneMatch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique case (sel)\n"
      "      2'b00: y = 0;\n"
      "      2'b01: y = 1;\n"
      "      2'b10: y = 2;\n"
      "      2'b11: y = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
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

TEST(CaseQualifierParsing, PriorityCaseFirstMatch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority case (sel)\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(ProcessParsing, UniqueCase) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    unique case (sel)\n"
      "      2'b00: y = 4'd0;\n"
      "      2'b01: y = 4'd1;\n"
      "      2'b10: y = 4'd2;\n"
      "      2'b11: y = 4'd3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
  ASSERT_EQ(stmt->case_items.size(), 4u);
}

TEST(ProceduralStatementParsing, UniqueCasezQualifier) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    unique casez (sel)\n"
      "      2'b1?: x = 1;\n"
      "      2'b01: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(ProcessParsing, PriorityCase) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] req;\n"
      "  logic [1:0] grant;\n"
      "  always_comb begin\n"
      "    priority case (1'b1)\n"
      "      req[0]: grant = 2'd0;\n"
      "      req[1]: grant = 2'd1;\n"
      "      req[2]: grant = 2'd2;\n"
      "      req[3]: grant = 2'd3;\n"
      "      default: grant = 2'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  ASSERT_EQ(stmt->case_items.size(), 5u);
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

TEST(ProcessParsing, AtStarUniqueCase) {
  auto r = Parse(
      "module m;\n"
      "  reg [1:0] sel;\n"
      "  reg out;\n"
      "  always @* begin\n"
      "    unique case (sel)\n"
      "      2'b00: out = 0;\n"
      "      2'b01: out = 1;\n"
      "      default: out = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  auto* case_stmt = GetAlwaysStarCaseStmt(r);
  ASSERT_NE(case_stmt, nullptr);
  EXPECT_EQ(case_stmt->qualifier, CaseQualifier::kUnique);
}

TEST(CaseQualifierParsing, PriorityCaseWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority case (opcode)\n"
      "      4'h0: result = a + b;\n"
      "      4'h1: result = a - b;\n"
      "      4'h2: result = a & b;\n"
      "      default: result = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  EXPECT_TRUE(HasDefaultCaseItem(stmt));
}

TEST(ProcessParsing, Unique0Case) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    unique0 case (sel)\n"
      "      2'b00: y = 4'd0;\n"
      "      2'b01: y = 4'd1;\n"
      "      2'b10: y = 4'd2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
  ASSERT_EQ(stmt->case_items.size(), 3u);
}

TEST(ProcessParsing, UniqueCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] q, a, b, c;\n"
      "  always_latch\n"
      "    unique case (sel)\n"
      "      2'b00: q <= a;\n"
      "      2'b01: q <= b;\n"
      "      2'b10: q <= c;\n"
      "      default: q <= q;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->qualifier, CaseQualifier::kUnique);
}

TEST(ProcessParsing, PriorityCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] q, a, b;\n"
      "  always_latch\n"
      "    priority case (sel)\n"
      "      2'b00: q <= a;\n"
      "      2'b01: q <= b;\n"
      "      default: q <= q;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->qualifier, CaseQualifier::kPriority);
}

TEST(CaseSyntaxParsing, PriorityCaseParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority case(x)\n"
      "      0: y = 1;\n"
      "      1: y = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
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

TEST(ProceduralStatementParsing, Unique0CaseWithDefault) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    unique0 case (sel)\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "      default: ;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
  ASSERT_GE(stmt->case_items.size(), 3u);
  EXPECT_TRUE(stmt->case_items[2].is_default);
}

TEST(ProcessParsing, Unique0CaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] q, a, b;\n"
      "  always_latch\n"
      "    unique0 case (sel)\n"
      "      2'b00: q <= a;\n"
      "      2'b01: q <= b;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->qualifier, CaseQualifier::kUnique0);
}

TEST(ProceduralStatementParsing, UniqueCasexQualifier) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    unique casex (sel)\n"
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
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(CaseQualifierParsing, Unique0Casez) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 casez (sel)\n"
      "      4'b1???: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
}

TEST(CaseQualifierParsing, Unique0Casex) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 casex (sel)\n"
      "      4'b1xxx: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
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
