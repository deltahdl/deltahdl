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

}  // namespace
