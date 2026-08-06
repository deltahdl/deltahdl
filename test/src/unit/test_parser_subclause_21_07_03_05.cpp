#include "fixture_parser.h"

using namespace delta;

namespace {

// Syntax 21-25: the $dumpportsflush task names a $dumpports output to flush.
TEST(IoSystemTaskParsing, DumpportsflushCallWithFileName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsflush(\"ports.vcd\");\n"
              "endmodule\n"));
}

// §21.7.3.5: the filename is optional. With no filename the flush covers every
// file opened by $dumpports, so the empty-argument form is accepted.
TEST(IoSystemTaskParsing, DumpportsflushEmptyParenCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsflush();\n"
              "endmodule\n"));
}

// §21.7.3.5: the no-filename default action is equally reachable through the
// bare task name with no argument list at all.
TEST(IoSystemTaskParsing, DumpportsflushBareCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsflush;\n"
              "endmodule\n"));
}

// Syntax 21-25: the filename is an expression, so an identifier -- the form a
// string-typed or integral variable holding the name takes -- parses in the
// filename position.
TEST(IoSystemTaskParsing, DumpportsflushVariableFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsflush(fname);\n"
              "endmodule\n"));
}

// Syntax 21-25: a composite filename expression, such as a concatenation
// assembling the name from parts, also parses in the filename position.
TEST(IoSystemTaskParsing, DumpportsflushExpressionFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsflush({stem, \".vcd\"});\n"
              "endmodule\n"));
}

// Syntax 21-25: the task statement is not limited to initial blocks -- a call
// inside a task body parses in that statement position too.
TEST(IoSystemTaskParsing, DumpportsflushInsideTaskBody) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  task do_flush;\n"
              "    $dumpportsflush(\"ports.vcd\");\n"
              "  endtask\n"
              "endmodule\n"));
}

// Syntax 21-25 negative: the filename requires a parenthesized argument list;
// a name butted against the task keyword without parentheses does not parse.
TEST(IoSystemTaskParsing, DumpportsflushUnparenthesizedFilenameRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  initial $dumpportsflush \"ports.vcd\";\n"
              "endmodule\n"));
}

}  // namespace
