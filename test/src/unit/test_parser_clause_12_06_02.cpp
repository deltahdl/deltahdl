// §12.6.2: Pattern matching in if statements

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// pattern ::= . variable_identifier
// ---------------------------------------------------------------------------
// §12.6: pattern with identifier binding (.name)
TEST(ParserA60701, PatternDotIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (v matches .n) x = n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// pattern ::= .*
// ---------------------------------------------------------------------------
// §12.6: wildcard pattern .*
TEST(ParserA60701, PatternWildcard) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (v matches .*) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
