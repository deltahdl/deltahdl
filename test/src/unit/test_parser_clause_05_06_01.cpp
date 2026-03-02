// §5.6.1: Escaped identifiers

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA212, LetIdentifier_Escaped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let \\my+let = 1;\n"
              "endmodule\n"));
}

// =============================================================================
// A.8.4 Primaries — escaped identifier as primary
// =============================================================================
// § primary — escaped identifier
TEST(ParserA84, PrimaryEscapedIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  logic \\my-signal ;\n"
      "  initial \\my-signal = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
