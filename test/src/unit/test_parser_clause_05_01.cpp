#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, ArrayLiteralParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int arr [0:1];\n"
              "  initial arr = '{0, 1};\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, BuiltinMethodCallParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int q[$];\n"
              "  int sz;\n"
              "  initial sz = q.size();\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, BuiltinMethodCallWithoutParensParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int q[$];\n"
              "  int sz;\n"
              "  initial sz = q.size;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, AllFourAreasInOneParse) {
  EXPECT_TRUE(
      ParseOk("(* optimize *) module t;\n"
              "  logic [7:0] data = 8'hFF;\n"
              "  real pi = 3.14;\n"
              "  initial begin\n"
              "    $display(\"all areas: %d %f\", data, pi);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
