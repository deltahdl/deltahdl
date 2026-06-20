#include "fixture_parser.h"

using namespace delta;

namespace {

// Syntax 21-19: dumpflush_task ::= $dumpflush ; — the $dumpflush task takes no
// arguments, so the bare invocation is accepted by the parser.
TEST(IoSystemTaskParsing, DumpflushNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpvars;\n"
              "    $dumpflush;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
