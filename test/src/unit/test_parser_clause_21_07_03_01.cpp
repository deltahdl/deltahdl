// §21.7.3.1: Specifying dump file name and ports to be dumped ($dumpports)

#include "fixture_parser.h"

using namespace delta;

namespace {

// ============================================================================
// Additional coverage -- VCD port dump tasks from 21.1 overview
// ============================================================================
TEST(ParserSection21, DumpportsCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpports(t, \"ports.vcd\");\n"
              "endmodule\n"));
}

}  // namespace
