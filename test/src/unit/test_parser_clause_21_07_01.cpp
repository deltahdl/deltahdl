// §21.7.1: Creating 4-state VCD file

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, DumpallAndFlush) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpvars;\n"
              "    #50 $dumpall;\n"
              "    #50 $dumpflush;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection21, DumpvarsInInitialBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpfile(\"module1.dump\");\n"
              "    $dumpvars(0, t);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection21, FullVcdWorkflow) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg clk;\n"
              "  initial begin\n"
              "    $dumpfile(\"dump1.dump\");\n"
              "    $dumpvars(0, t);\n"
              "    #10 $dumpoff;\n"
              "    #200 $dumpon;\n"
              "    #800 $dumpoff;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
