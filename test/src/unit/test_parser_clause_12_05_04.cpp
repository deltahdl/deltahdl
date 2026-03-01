// §12.5.4: Set membership case statement

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// case_statement ::=
//   [ unique_priority ] case ( case_expression ) inside
//     case_inside_item { case_inside_item } endcase
// ---------------------------------------------------------------------------
// §12.5.4: case-inside variant
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

// =============================================================================
// LRM section 12.5.4 -- case inside
// =============================================================================
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

// ---------------------------------------------------------------------------
// case_inside_item ::=
//   range_list : statement_or_null
// range_list ::= value_range { , value_range }
// ---------------------------------------------------------------------------
// §12.5.4: case inside with range [lo:hi]
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

// §12.5.4: case inside with multiple value_ranges (comma-separated)
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

// ---------------------------------------------------------------------------
// value_range ::= expression
// value_range ::= [ expression : expression ]
// ---------------------------------------------------------------------------
// §11.4.13: value_range as simple expression in case-inside
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

}  // namespace
