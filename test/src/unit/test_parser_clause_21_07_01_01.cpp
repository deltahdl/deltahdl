#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumpfileBasic) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpfile(\"dump.vcd\");\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpfileDefaultName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpfile;\n"
              "endmodule\n"));
}

}  // namespace
