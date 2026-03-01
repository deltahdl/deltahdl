// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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
