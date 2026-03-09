#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, DumpportsCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpports(t, \"ports.vcd\");\n"
              "endmodule\n"));
}

}  // namespace
