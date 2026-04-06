#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CaseInsideSyntaxParsing, CaseInsideStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (val) inside\n"
      "      [0:5]: a = 1;\n"
      "      [6:10]: a = 2;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_TRUE(stmt->case_inside);
}

TEST(CaseInsideSyntaxParsing, CaseInsideCommaValuesAndRange) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) inside\n"
      "      1, 3: y = 8'd10;\n"
      "      [4:7]: y = 8'd20;\n"
      "      default: y = 8'd30;\n"
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

TEST(CaseInsideSyntaxParsing, CaseInsideScalarValues) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (val) inside\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_TRUE(stmt->case_inside);
}

TEST(CaseInsideSyntaxParsing, CaseInsideRange) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) inside\n"
      "      [0:3]: y = 1;\n"
      "      [4:7]: y = 2;\n"
      "      default: y = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_inside);
  ASSERT_GE(stmt->case_items.size(), 2u);
}

TEST(CaseInsideSyntaxParsing, CaseInsideMultipleRanges) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) inside\n"
      "      1, 3, [5:7]: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_inside);
  EXPECT_EQ(stmt->case_items[0].patterns.size(), 3u);
}

TEST(CaseInsideSyntaxParsing, ValueRangeExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) inside\n"
      "      5: y = 1;\n"
      "      10: y = 2;\n"
      "      default: y = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CaseInsideSyntaxParsing, ValueRangeBracket) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) inside\n"
      "      [0:15]: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CaseInsideSyntaxParsing, ValueRangeOpenEndedLow) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (x) inside\n"
      "      [$:5]: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_inside);
  ASSERT_GE(stmt->case_items.size(), 1u);
  auto* pat = stmt->case_items[0].patterns[0];
  EXPECT_EQ(pat->kind, ExprKind::kSelect);
}

TEST(CaseInsideSyntaxParsing, ValueRangeOpenEndedHigh) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (x) inside\n"
      "      [5:$]: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_inside);
  ASSERT_GE(stmt->case_items.size(), 1u);
  auto* pat = stmt->case_items[0].patterns[0];
  EXPECT_EQ(pat->kind, ExprKind::kSelect);
}

TEST(CaseInsideSyntaxParsing, ValueRangePlusMinus) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (x) inside\n"
      "      [5 +/- 2]: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_inside);
  ASSERT_GE(stmt->case_items.size(), 1u);
  auto* pat = stmt->case_items[0].patterns[0];
  EXPECT_EQ(pat->kind, ExprKind::kSelect);
  EXPECT_EQ(pat->op, TokenKind::kPlusSlashMinus);
}

TEST(CaseInsideSyntaxParsing, ValueRangePlusPercentMinus) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (x) inside\n"
      "      [50 +%- 10]: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_inside);
  ASSERT_GE(stmt->case_items.size(), 1u);
  auto* pat = stmt->case_items[0].patterns[0];
  EXPECT_EQ(pat->kind, ExprKind::kSelect);
  EXPECT_EQ(pat->op, TokenKind::kPlusPercentMinus);
}

TEST(CaseInsideSyntaxParsing, CasexInsideIsError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    casex (sel) inside\n"
      "      0: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(CaseInsideSyntaxParsing, CasezInsideIsError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    casez (sel) inside\n"
      "      0: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(CaseInsideSyntaxParsing, CaseInsideWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (x) inside\n"
      "      8'd1: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_inside);
  EXPECT_TRUE(HasDefaultCaseItem(stmt));
}

TEST(CaseInsideSyntaxParsing, CaseInsideEmptyNoItems) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (x) inside\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_inside);
  EXPECT_EQ(stmt->case_items.size(), 0u);
}

}  // namespace
