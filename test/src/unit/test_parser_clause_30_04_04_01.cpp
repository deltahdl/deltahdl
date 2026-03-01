// §30.4.4.1: Conditional expression

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.8.6 Operators — unary_module_path_operator
// =============================================================================
// § unary_module_path_operator — ! in specify path condition
TEST(ParserA86, UnaryModulePathNot) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (!a) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § unary_module_path_operator — ~ in specify path condition
TEST(ParserA86, UnaryModulePathBitwiseNot) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (~a) (a => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — != in specify path condition
TEST(ParserA86, BinaryModulePathNeq) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a != b) (a => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — || in specify path condition
TEST(ParserA86, BinaryModulePathLogicalOr) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a || b) (a => y) = 4;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
