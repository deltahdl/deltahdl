#include "fixture_parser.h"

using namespace delta;

namespace {

// Syntax 21-18: dumplimit_task ::= $dumplimit ( filesize ) ; -- a task enable
// carrying one required parenthesized filesize argument and terminated by a
// semicolon. The tests cover the argument forms filesize can take and the
// syntactic positions the task enable can occupy.

// The canonical shape: a literal filesize inside the dump-task idiom of an
// initial begin-end block.
TEST(IoSystemTaskParsing, DumplimitCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpfile(\"out.vcd\");\n"
              "    $dumplimit(1000000);\n"
              "    $dumpvars;\n"
              "  end\n"
              "endmodule\n"));
}

// A bare statement needs no begin-end: the task parses as the sole statement
// of an initial construct behind a delay control.
TEST(IoSystemTaskParsing, DumplimitAsSoleStatement) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial #5 $dumplimit(4096);\n"
              "endmodule\n"));
}

// The task is an ordinary statement inside an always procedure.
TEST(IoSystemTaskParsing, DumplimitInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic clk;\n"
              "  always @(posedge clk) begin\n"
              "    $dumplimit(4096);\n"
              "  end\n"
              "endmodule\n"));
}

// The task is an ordinary statement inside a task body.
TEST(IoSystemTaskParsing, DumplimitInTaskBody) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  task cap;\n"
              "    $dumplimit(4096);\n"
              "  endtask\n"
              "endmodule\n"));
}

// filesize is an expression: a parameter reference is an accepted argument.
TEST(IoSystemTaskParsing, DumplimitParameterFilesize) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  parameter LIMIT = 200;\n"
              "  initial $dumplimit(LIMIT);\n"
              "endmodule\n"));
}

// filesize is an expression: an arithmetic expression is an accepted argument.
TEST(IoSystemTaskParsing, DumplimitExpressionFilesize) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumplimit(2 * 512);\n"
              "endmodule\n"));
}

// Negative: the production requires the terminating semicolon, so a
// $dumplimit task enable running straight into the block end is rejected.
TEST(IoSystemTaskParsing, DumplimitMissingSemicolonRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumplimit(200)\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
