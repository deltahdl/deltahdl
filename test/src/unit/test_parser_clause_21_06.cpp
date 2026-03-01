// §21.6: Command line input

#include "fixture_parser.h"

using namespace delta;

namespace {

// ============================================================================
// Additional coverage -- Command line input from 21.1 overview
// ============================================================================
TEST(ParserSection21, TestPlusargsCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    if ($test$plusargs(\"VERBOSE\"))\n"
              "      $display(\"verbose mode\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection21, ValuePlusargsCall) {
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
