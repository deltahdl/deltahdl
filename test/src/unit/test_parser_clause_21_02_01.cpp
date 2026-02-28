// §21.2.1: The display and write tasks

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, DisplayInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg clk;\n"
              "  always @(posedge clk)\n"
              "    $display(\"clock edge at %0t\", $time);\n"
              "endmodule\n"));
}

}  // namespace
