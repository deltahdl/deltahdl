#include "fixture_parser.h"

using namespace delta;

namespace {

// Syntax 21-24: the filesize-only form, where the limit covers every file
// opened by $dumpports.
TEST(IoSystemTaskParsing, DumpportslimitCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportslimit(500000);\n"
              "endmodule\n"));
}

// Syntax 21-24: the filesize-plus-filename form, naming the $dumpports output
// the limit applies to.
TEST(IoSystemTaskParsing, DumpportslimitCallWithFileName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportslimit(500000, \"ports.vcd\");\n"
              "endmodule\n"));
}

}  // namespace
