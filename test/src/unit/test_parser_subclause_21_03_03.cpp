#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, SwriteBasic) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  string s;\n"
              "  initial $swrite(s, \"value=%d\", 42);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, SwritebHexOctal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  string s;\n"
              "  initial begin\n"
              "    $swriteb(s, val);\n"
              "    $swriteh(s, val);\n"
              "    $swriteo(s, val);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, SformatBasic) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  string s;\n"
              "  initial $sformat(s, \"data is %d\", 123);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, SformatNoExtraArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  string s;\n"
              "  initial $sformat(s, \"no args here\");\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, SformatfInExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  string s;\n"
              "  initial s = $sformatf(\"val=%0d\", 42);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, SwriteOutputVarOnly) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  string s;\n"
              "  initial $swrite(s);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, SformatfFormatOnly) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  string s;\n"
              "  initial s = $sformatf(\"plain text\");\n"
              "endmodule\n"));
}

}  // namespace
