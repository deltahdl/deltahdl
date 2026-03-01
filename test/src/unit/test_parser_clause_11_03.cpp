// §11.3: Operators

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- Additional all-operator coverage ---
TEST(ParserSection11, Sec11_1_AllBinaryOperatorsParse) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    x = a + b;\n"
              "    x = a - b;\n"
              "    x = a * b;\n"
              "    x = a / b;\n"
              "    x = a % b;\n"
              "    x = a ** b;\n"
              "    x = a == b;\n"
              "    x = a != b;\n"
              "    x = a === b;\n"
              "    x = a !== b;\n"
              "    x = a < b;\n"
              "    x = a <= b;\n"
              "    x = a > b;\n"
              "    x = a >= b;\n"
              "    x = a && b;\n"
              "    x = a || b;\n"
              "    x = a & b;\n"
              "    x = a | b;\n"
              "    x = a ^ b;\n"
              "    x = a ~^ b;\n"
              "    x = a ^~ b;\n"
              "    x = a << b;\n"
              "    x = a >> b;\n"
              "    x = a <<< b;\n"
              "    x = a >>> b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection11, Sec11_1_AllUnaryOperatorsParse) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    x = +a;\n"
              "    x = -a;\n"
              "    x = ~a;\n"
              "    x = !a;\n"
              "    x = &a;\n"
              "    x = |a;\n"
              "    x = ^a;\n"
              "    x = ~&a;\n"
              "    x = ~|a;\n"
              "    x = ~^a;\n"
              "    x = ^~a;\n"
              "  end\n"
              "endmodule\n"));
}

// =========================================================================
// All single-char operators parse correctly
// =========================================================================
TEST(ParserCh501, Sec5_1_SingleCharOperators) {
  // Exercise +, -, *, /, %, &, |, ^, ~ as single-character operators.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = a + b;\n"
              "    x = a - b;\n"
              "    x = a * b;\n"
              "    x = a / b;\n"
              "    x = a % b;\n"
              "    x = a & b;\n"
              "    x = a | b;\n"
              "    x = a ^ b;\n"
              "    x = ~a;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
