#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, TestPlusargsCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    if ($test$plusargs(\"VERBOSE\"))\n"
              "      $display(\"verbose mode\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, ValuePlusargsCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer depth;\n"
              "  initial begin\n"
              "    if ($value$plusargs(\"DEPTH=%d\", depth))\n"
              "      $display(\"depth=%0d\", depth);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
