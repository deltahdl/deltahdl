// §21.7.1.3: Stopping and resuming the dump ($dumpoff/$dumpon)

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, DumpOffOnSequence) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpvars;\n"
              "    #100 $dumpoff;\n"
              "    #200 $dumpon;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
