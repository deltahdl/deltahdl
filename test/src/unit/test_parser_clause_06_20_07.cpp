// §6.20.7: $ as a constant

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § primary — $
TEST(ParserA84, PrimaryDollar) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
