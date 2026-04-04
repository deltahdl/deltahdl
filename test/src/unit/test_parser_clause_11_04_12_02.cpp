#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(OperatorAndExpressionParsing, StringConcatenation) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  string hello, s;\n"
              "  initial begin\n"
              "    hello = \"hello\";\n"
              "    s = {hello, \" \", \"world\"};\n"
              "  end\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, StringReplication) {
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

}  // namespace
