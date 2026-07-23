#include "fixture_parser.h"

using namespace delta;

namespace {

// Syntax 21-17: dumpall_task ::= $dumpall ; -- an argument-less task enable
// terminated by a semicolon. The tests cover the syntactic positions a task
// enable can occupy.

// The canonical shape: $dumpall follows $dumpvars and a delay control inside
// an initial begin-end block.
TEST(IoSystemTaskParsing, DumpallNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpvars;\n"
              "    #50 $dumpall;\n"
              "  end\n"
              "endmodule\n"));
}

// A bare statement needs no begin-end: the task parses as the sole statement
// of an initial construct behind a delay control.
TEST(IoSystemTaskParsing, DumpallAsSoleStatement) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial #5 $dumpall;\n"
              "endmodule\n"));
}

// The task is an ordinary statement inside an always procedure.
TEST(IoSystemTaskParsing, DumpallInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic clk;\n"
              "  always @(posedge clk) begin\n"
              "    $dumpall;\n"
              "  end\n"
              "endmodule\n"));
}

// The task is an ordinary statement inside a task body.
TEST(IoSystemTaskParsing, DumpallInTaskBody) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  task snapshot;\n"
              "    $dumpall;\n"
              "  endtask\n"
              "endmodule\n"));
}

// Negative: the production requires the terminating semicolon, so a $dumpall
// task enable running straight into the block end is rejected.
TEST(IoSystemTaskParsing, DumpallMissingSemicolonRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpall\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
