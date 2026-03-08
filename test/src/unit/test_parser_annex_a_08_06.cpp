// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §A.8.6 — unary_module_path_operator
TEST(ParserA86, UnaryModulePathNot) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (!a) (a => y) = 9;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA86, UnaryModulePathBitwiseNot) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (~a) (a => y) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA86, UnaryModulePathReductionAnd) {
  auto r = Parse(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (&a) (a[0] => y) = 11;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
