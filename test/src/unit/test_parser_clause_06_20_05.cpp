// §6.20.5: Specify parameters

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA24, SpecparamAssignmentMintypmax) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tDelay = 1:2:3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
