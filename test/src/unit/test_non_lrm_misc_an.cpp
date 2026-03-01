// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.7 Case statements
// =============================================================================
// ---------------------------------------------------------------------------
// case_statement ::=
//   [ unique_priority ] case_keyword ( case_expression )
//     case_item { case_item } endcase
// ---------------------------------------------------------------------------
// §12.5: basic case statement with single items
TEST(ParserA607, CaseStmtParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) 0: y = 1; default: y = 0; endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCase);
}

// §11.4.13: value_range with bracket range [lo:hi]
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

// §12.5: case with null statement body (;)
TEST(ParserA607, CaseItemNullBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x)\n"
      "      0: ;\n"
      "      1: y = 1;\n"
      "      default: ;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 3u);
}

// §12.5: case with expression as case_expression (not just identifier)
TEST(ParserA607, CaseComplexExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(a + b)\n"
      "      0: y = 1;\n"
      "      1: y = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
}

}  // namespace
