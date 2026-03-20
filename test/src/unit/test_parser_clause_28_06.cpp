// §28.6

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(EnableGates, TooManyTerminals) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 b1(out, in, en, extra);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
