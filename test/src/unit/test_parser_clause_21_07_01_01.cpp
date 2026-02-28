// §21.7.1.1: Specifying name of dump file ($dumpfile)

#include "fixture_parser.h"

using namespace delta;

namespace {

// ============================================================================
// LRM section 21.7.1 -- Creating 4-state VCD file ($dumpfile, $dumpvars,
//                        $dumpoff, $dumpon, $dumpall, $dumpflush, $dumplimit)
// ============================================================================
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
