#include "fixture_parser.h"

using namespace delta;

namespace {

// §21.7.3.3 (Syntax 21-23): the $dumpportsall task takes a single filename
// argument and parses as a generic system task call.
TEST(IoSystemTaskParsing, DumpportsallCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsall(\"ports.vcd\");\n"
              "endmodule\n"));
}

// §21.7.3.3: the filename argument is optional; the no-argument form checkpoints
// every file opened by $dumpports.
TEST(IoSystemTaskParsing, DumpportsallNoFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsall;\n"
              "endmodule\n"));
}

}
