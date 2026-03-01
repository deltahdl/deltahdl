// §12.5.2: Constant expression in case statement

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §12.5.2: constant expression as case_expression
TEST(ParserA607, ConstExprCaseExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(1)\n"
      "      a: y = 1;\n"
      "      b: y = 2;\n"
      "      default: y = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_NE(stmt->condition, nullptr);
}

}  // namespace
