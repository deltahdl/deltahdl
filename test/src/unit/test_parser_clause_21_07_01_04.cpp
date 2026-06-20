#include "fixture_parser.h"

using namespace delta;

namespace {

// Syntax 21-17: dumpall_task ::= $dumpall ; — the $dumpall task takes no
// arguments, so the bare invocation is accepted by the parser.
TEST(IoSystemTaskParsing, DumpallNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpvars;\n"
              "    #50 $dumpall;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
