// §12.6.1: Pattern matching in case statements

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.7.1 Patterns — Parsing tests
// =============================================================================
// ---------------------------------------------------------------------------
// pattern ::= constant_expression
// ---------------------------------------------------------------------------
// §12.6: pattern as constant expression in case-matches
TEST(ParserA60701, PatternConstantExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) matches\n"
      "      5: y = 8'd10;\n"
      "      10: y = 8'd20;\n"
      "      default: y = 8'd30;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
