// §28.9

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CmosSwitches, TooManyTerminals) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(out, data, nctrl, pctrl, extra);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
