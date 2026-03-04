#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection11, StringConcatenation) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  string hello, s;\n"
              "  initial begin\n"
              "    hello = \"hello\";\n"
              "    s = {hello, \" \", \"world\"};\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection11, StringReplication) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    int n;\n"
              "    string s;\n"
              "    n = 3;\n"
              "    s = {n{\"boo \"}};\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, StringConcatOp) {

  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  string a, b, c;\n"
              "  initial begin\n"
              "    a = \"hello\";\n"
              "    b = \" world\";\n"
              "    c = {a, b};\n"
              "  end\n"
              "endmodule\n"));
}

}
