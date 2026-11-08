#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(SubroutineCallExprParsing, RandomizeCallResultDiscarded) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SubroutineCallExprParsing, RandomizeCallReturnValueUsed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int success;\n"
      "    success = obj.randomize();\n"
      "    if (success == 1) success = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
