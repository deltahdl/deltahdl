#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(OptionalSystemTaskParserParsing, ShowVarsNoArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $showvars;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(OptionalSystemTaskParserParsing, ShowVarsVariableList) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial $showvars(a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(OptionalSystemTaskParserParsing, ShowVarsSelectArgument) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] v;\n"
      "  initial $showvars(v[3], v[5:2]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(OptionalSystemTaskParserParsing, ShowVarsSingleVariable) {
  auto r = Parse(
      "module m;\n"
      "  reg x;\n"
      "  initial $showvars(x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(OptionalSystemTaskParserParsing, ShowVarsIndexedPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] v;\n"
      "  initial $showvars(v[2+:3]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
