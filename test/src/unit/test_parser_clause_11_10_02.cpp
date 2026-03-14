#include "fixture_parser.h"

using namespace delta;
namespace {

TEST(StringLiteralPaddedParsing, StringLiteralToWiderVector) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  bit [8*10:1] s;\n"
              "  initial s = \"Hello\";\n"
              "endmodule\n"));
}

TEST(StringLiteralPaddedParsing, PaddedConcatCompareParses) {
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
