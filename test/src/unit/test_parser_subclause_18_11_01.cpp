#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;
namespace {

TEST(SubroutineCallExprParsing, RandomizeCallWithNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(null); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SubroutineCallExprParsing, BareRandomizeCallWithNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin randomize(null); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
