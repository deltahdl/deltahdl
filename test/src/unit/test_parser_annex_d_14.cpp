#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(OptionalSreadmemParser, SreadmemhBasicForm) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial $sreadmemh(mem, 0, 3, \"0A 14 1E\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OptionalSreadmemParser, SreadmembBasicForm) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial $sreadmemb(mem, 0, 3, \"1010 0110\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OptionalSreadmemParser, MultipleDataStrings) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial $sreadmemh(mem, 0, 3, \"0A 14\", \"1E 28\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
