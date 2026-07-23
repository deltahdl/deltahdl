#include "fixture_parser.h"

using namespace delta;

namespace {

// Syntax 21-19: dumpflush_task ::= $dumpflush ; -- a task enable with no
// argument list, terminated by a semicolon. The tests cover the syntactic
// positions the task enable can occupy and the missing-semicolon reject.

// The canonical shape of the LRM example: the bare invocation follows
// $dumpvars inside an initial begin-end block.
TEST(IoSystemTaskParsing, DumpflushNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpvars;\n"
              "    $dumpflush;\n"
              "  end\n"
              "endmodule\n"));
}

// A bare statement needs no begin-end: the task parses as the sole statement
// of an initial construct behind a delay control.
TEST(IoSystemTaskParsing, DumpflushAsSoleStatement) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial #5 $dumpflush;\n"
              "endmodule\n"));
}

// The task is an ordinary statement inside an always procedure.
TEST(IoSystemTaskParsing, DumpflushInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic clk;\n"
              "  always @(posedge clk) begin\n"
              "    $dumpflush;\n"
              "  end\n"
              "endmodule\n"));
}

// The task is an ordinary statement inside a task body.
TEST(IoSystemTaskParsing, DumpflushInTaskBody) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  task sync_dump;\n"
              "    $dumpflush;\n"
              "  endtask\n"
              "endmodule\n"));
}

// Negative: the production requires the terminating semicolon, so a
// $dumpflush task enable running straight into the block end is rejected.
TEST(IoSystemTaskParsing, DumpflushMissingSemicolonRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpflush\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
