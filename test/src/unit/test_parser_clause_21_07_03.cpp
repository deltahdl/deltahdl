#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumpportsOffOnFlush) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpports(t, \"ports.vcd\");\n"
              "    #100 $dumpportsoff;\n"
              "    #200 $dumpportson;\n"
              "    #300 $dumpportsflush;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
