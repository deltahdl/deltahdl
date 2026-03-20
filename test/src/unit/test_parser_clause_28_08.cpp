// §28.8

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(PassSwitches, SingleTerminal) {
  auto r = Parse(
      "module m;\n"
      "  tran t1(a);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
