#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA607, CaseInsideParse) {
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

TEST(ParserSection12, CaseInside) {
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

TEST(ParserA607, CaseInsideRange) {
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

TEST(ParserA607, CaseInsideMultipleRanges) {
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

TEST(ParserA607, ValueRangeExpression) {
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

TEST(ParserA607, ValueRangeBracket) {
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

}  // namespace
