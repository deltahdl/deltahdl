// §13.8: Parameterized tasks and functions

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §13.8: Parameterized class with type parameter.
TEST(ParserSection13, Sec13_8_TypeParameter) {
  EXPECT_TRUE(
      ParseOk("virtual class Converter#(parameter type T = int);\n"
              "  static function T identity(input T val);\n"
              "    return val;\n"
              "  endfunction\n"
              "endclass\n"));
}

// §13.8: Static method with return value used in expression.
TEST(ParserSection13, Sec13_8_StaticMethodInExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int val;\n"
              "  assign val = Utils#(8)::max_val() + 1;\n"
              "endmodule\n"));
}

}  // namespace
