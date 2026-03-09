#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, DumpfileBasic) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpfile(\"dump.vcd\");\n"
              "endmodule\n"));
}

TEST(ParserSection21, DumpfileDefaultName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpfile;\n"
              "endmodule\n"));
}

}  // namespace
