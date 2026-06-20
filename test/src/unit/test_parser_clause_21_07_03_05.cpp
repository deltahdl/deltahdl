#include "fixture_parser.h"

using namespace delta;

namespace {

// Syntax 21-25: the $dumpportsflush task names a $dumpports output to flush.
TEST(IoSystemTaskParsing, DumpportsflushCallWithFileName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsflush(\"ports.vcd\");\n"
              "endmodule\n"));
}

// §21.7.3.5: the filename is optional. With no filename the flush covers every
// file opened by $dumpports, so the empty-argument form is accepted.
TEST(IoSystemTaskParsing, DumpportsflushCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsflush();\n"
              "endmodule\n"));
}

}  // namespace
