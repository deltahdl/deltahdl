#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;
namespace {

TEST(RangeSystemFunctionParsing, IsUnboundedInConditional) {
  auto r = Parse(
      "module m #(parameter int N = $);\n"
      "  generate\n"
      "    if (!$isunbounded(N)) begin\n"
      "      assign out = in;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(RangeSystemFunctionParsing, IsUnboundedWithHierarchicalParam) {
  auto r = Parse(
      "module sub #(parameter int P = $);\n"
      "endmodule\n"
      "module top;\n"
      "  sub s();\n"
      "  initial if ($isunbounded(s.P)) $display(\"unbounded\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
