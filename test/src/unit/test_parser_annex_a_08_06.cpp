#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA86, BinaryModulePathEq) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a == b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA86, BinaryModulePathBitwiseOr) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a | b) (a => y) = 6;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA86, BinaryModulePathXor) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ^ b) (a => y) = 7;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA86, BinaryModulePathXnor) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ^~ b) (a => y) = 8;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
