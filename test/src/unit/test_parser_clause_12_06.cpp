// §12.6: Pattern matching conditional statements

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// pattern ::= ( pattern )
// ---------------------------------------------------------------------------
// §12.6: parenthesized pattern
TEST(ParserA60701, PatternParenthesized) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (e matches (tagged Valid .n)) x = n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
