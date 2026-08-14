#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(OperatorAndExpressionParsing, InsideWithRangeElements) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {[16:23], [32:47]}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->elements.size(), 2u);
}

TEST(OperatorAndExpressionParsing, InsideWithWildcardBits) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [2:0] val;\n"
              "  initial begin\n"
              "    while (val inside {3'b1?1}) val = val + 1;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, InsideWithDollarRange) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int a;\n"
              "  initial begin\n"
              "    if (a inside {[$:10]}) a = 0;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, InsideWithDollarUpperBound) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int a;\n"
              "  initial begin\n"
              "    if (a inside {[10:$]}) a = 0;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, InsideAbsToleranceRange) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {[5 +/- 2]}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
  EXPECT_EQ(cond->elements.size(), 1u);
  EXPECT_EQ(cond->elements[0]->kind, ExprKind::kSelect);
  EXPECT_EQ(cond->elements[0]->op, TokenKind::kPlusSlashMinus);
}

TEST(OperatorAndExpressionParsing, InsideRelToleranceRange) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {[50 +%- 10]}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
  EXPECT_EQ(cond->elements.size(), 1u);
  EXPECT_EQ(cond->elements[0]->op, TokenKind::kPlusPercentMinus);
}

TEST(OperatorAndExpressionParsing, InsideMixedValuesAndRanges) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {1, [5:10], 20, [30:40]}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
  EXPECT_EQ(cond->elements.size(), 4u);
}

TEST(ExpressionParsing, InsideExprSingleValue) {
  auto r = Parse("module m; initial x = a inside {3}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kInside);
  EXPECT_EQ(rhs->elements.size(), 1u);
}

TEST(ExpressionParsing, InsideExprWithRange) {
  auto r = Parse("module m; initial x = a inside {[1:10]}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kInside);
  EXPECT_EQ(rhs->elements.size(), 1u);

  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kSelect);
}

TEST(OperatorAndExpressionParsing, InsideExpressionWithLhsAndElements) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (val inside {1, 2, 3}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
  ASSERT_NE(cond->lhs, nullptr);
  EXPECT_EQ(cond->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(cond->elements.size(), 3u);
}

// Covers Parser::ParseInsideValueRange in src/parser/expr_parser_patterns.cpp,
// which builds the ExprKind::kSelect that one bracketed element of an
// open_range_list becomes. It assigned no range.start before this commit, so a
// report standing at such an element printed "<unknown location>" instead of a
// file, line and column. §11.4.13 writes the element as `[ expression :
// expression ]`, the bracketed pair itself, so it begins at the `[` rather than
// at either bound: column 25 of line 2.
TEST(OperatorAndExpressionParsing, InsideValueRangeStartsAtItsBracket) {
  auto r = Parse(
      "module t;\n"
      "  initial if (a inside {[1:2]}) x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->condition, nullptr);
  ASSERT_EQ(stmt->condition->elements.size(), 1u);
  auto* range = stmt->condition->elements[0];
  EXPECT_EQ(range->kind, ExprKind::kSelect);
  EXPECT_EQ(range->range.start.line, 2u);
  EXPECT_EQ(range->range.start.column, 25u);
}

}  // namespace
