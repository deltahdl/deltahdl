#include "fixture_parser.h"

using namespace delta;

namespace {

// Syntax 21-16: dumpoff_task ::= $dumpoff ; and dumpon_task ::= $dumpon ; --
// both tasks are argument-less task enables terminated by a semicolon. The
// tests cover the syntactic positions a task enable can occupy.

// The LRM example's shape: the tasks follow $dumpvars and delay controls
// inside an initial begin-end block, bounding the dump window twice.
TEST(IoSystemTaskParsing, DumpOffOnExampleSequence) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    #10  $dumpvars;\n"
              "    #200 $dumpoff;\n"
              "    #800 $dumpon;\n"
              "    #900 $dumpoff;\n"
              "  end\n"
              "endmodule\n"));
}

// A bare statement needs no begin-end: each task parses as the sole statement
// of an initial construct behind a delay control.
TEST(IoSystemTaskParsing, DumpOffOnAsSoleStatement) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial #5 $dumpoff;\n"
              "  initial #9 $dumpon;\n"
              "endmodule\n"));
}

// The tasks are ordinary statements inside an always procedure.
TEST(IoSystemTaskParsing, DumpOffOnInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic clk;\n"
              "  always @(posedge clk) begin\n"
              "    $dumpoff;\n"
              "    $dumpon;\n"
              "  end\n"
              "endmodule\n"));
}

// The tasks are ordinary statements inside a task body.
TEST(IoSystemTaskParsing, DumpOffOnInTaskBody) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  task pause_dump;\n"
              "    $dumpoff;\n"
              "  endtask\n"
              "  task resume_dump;\n"
              "    $dumpon;\n"
              "  endtask\n"
              "endmodule\n"));
}

// Negative: the production requires the terminating semicolon, so a $dumpoff
// task enable running straight into the block end is rejected.
TEST(IoSystemTaskParsing, DumpOffMissingSemicolonRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpoff\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
