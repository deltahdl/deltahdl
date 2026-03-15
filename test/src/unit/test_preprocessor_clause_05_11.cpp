#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ArrayLiteralPreprocessor, MacroInArrayLiteral) {
  auto r = ParseWithPreprocessor(
      "`define VAL0 10\n"
      "`define VAL1 20\n"
      "`define VAL2 30\n"
      "module m;\n"
      "  int arr [0:2] = '{`VAL0, `VAL1, `VAL2};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ArrayLiteralPreprocessor, MacroExpandsToReplicationCount) {
  auto r = ParseWithPreprocessor(
      "`define N 3\n"
      "module m;\n"
      "  int arr [0:2] = '{`N{0}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
