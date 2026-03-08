#include "fixture_parser.h"

using namespace delta;
namespace {

// §11.10.2: String literal assigned to wider vector parses correctly.
TEST(ParserSection1110_2, StringLiteralToWiderVector) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  bit [8*10:1] s;\n"
              "  initial s = \"Hello\";\n"
              "endmodule\n"));
}

// §11.10.2: Concatenation of padded vectors compared with string literal.
TEST(ParserSection1110_2, PaddedConcatCompareParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  bit [8*10:1] s1, s2;\n"
              "  logic result;\n"
              "  initial begin\n"
              "    s1 = \"Hello\";\n"
              "    s2 = \" world!\";\n"
              "    result = ({s1, s2} == \"Hello world!\");\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
