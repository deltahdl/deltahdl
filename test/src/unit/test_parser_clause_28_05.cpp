// §28.5

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(BufNotGates, SingleTerminal) {
  auto r = Parse(
      "module m;\n"
      "  buf b1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
