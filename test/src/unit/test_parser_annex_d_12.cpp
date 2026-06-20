#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Annex D.12: $showscopes may appear with no argument, parsing as an ordinary
// system task call.
TEST(OptionalSystemTaskParserParsing, ShowScopesNoArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $showscopes;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// Annex D.12: $showscopes accepts an optional integer argument in parentheses.
TEST(OptionalSystemTaskParserParsing, ShowScopesIntegerArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $showscopes(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
