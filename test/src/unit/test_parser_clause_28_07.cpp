// §28.7

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- Terminal count error cases not covered by subsection files ---
TEST(MosSwitches, TooFewTerminals) {
  auto r = Parse(
      "module m;\n"
      "  nmos n1(out, data);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
