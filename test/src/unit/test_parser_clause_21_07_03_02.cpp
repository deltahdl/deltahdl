#include "fixture_parser.h"

using namespace delta;

namespace {

// §21.7.3.2 (Syntax 21-22): the $dumpportsoff task takes a single filename
// argument and parses as a generic system task call.
TEST(IoSystemTaskParsing, DumpportsoffCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsoff(\"ports.vcd\");\n"
              "endmodule\n"));
}

// §21.7.3.2 (Syntax 21-22): the $dumpportson task takes a single filename
// argument and parses as a generic system task call.
TEST(IoSystemTaskParsing, DumpportsonCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportson(\"ports.vcd\");\n"
              "endmodule\n"));
}

// §21.7.3.2: the filename argument is optional; both tasks accept the
// no-argument form that targets every file opened by $dumpports.
TEST(IoSystemTaskParsing, DumpportsOffOnNoFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpportsoff;\n"
              "    $dumpportson;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
