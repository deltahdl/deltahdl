#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(NumberPreprocessor, ThreeTokenBasedLiteralFromMacros) {
  auto r = ParseWithPreprocessor(
      "`define SZ 8\n"
      "`define BF 'h\n"
      "`define VAL FF\n"
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = `SZ `BF `VAL;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
