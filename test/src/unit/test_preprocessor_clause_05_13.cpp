#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(BuiltinMethodPreprocessor, MacroInMethodArg) {
  auto r = ParseWithPreprocessor(
      "`define VAL 8'hAA\n"
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  initial q.push_back(`VAL);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(BuiltinMethodPreprocessor, MacroExpandsToMethodObject) {
  auto r = ParseWithPreprocessor(
      "`define ARR arr\n"
      "module m;\n"
      "  int arr [0:3];\n"
      "  int s;\n"
      "  initial s = `ARR.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
