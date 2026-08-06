#include "fixture_parser.h"

using namespace delta;

namespace {

// §21.7.3.2 (Syntax 21-22): the $dumpportsoff task takes a single filename
// argument and parses as a generic system task call.
TEST(IoSystemTaskParsing, DumpportsoffCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsoff(\"ports.vcd\");\n"
              "endmodule\n"));
}

// §21.7.3.2 (Syntax 21-22): the $dumpportson task takes a single filename
// argument and parses as a generic system task call.
TEST(IoSystemTaskParsing, DumpportsonCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportson(\"ports.vcd\");\n"
              "endmodule\n"));
}

// §21.7.3.2: the filename argument is optional; both tasks accept the
// no-argument form that targets every file opened by $dumpports.
TEST(IoSystemTaskParsing, DumpportsOffOnNoFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpportsoff;\n"
              "    $dumpportson;\n"
              "  end\n"
              "endmodule\n"));
}

// §21.7.3.2: leaving the filename unspecified also admits the empty
// parenthesized call form for both tasks.
TEST(IoSystemTaskParsing, DumpportsOffOnEmptyParenForms) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpportsoff();\n"
              "    $dumpportson();\n"
              "  end\n"
              "endmodule\n"));
}

// §21.7.3.2: the filename is an expression, so both tasks accept an identifier
// (a string-typed or integral variable holding the name) instead of a literal.
TEST(IoSystemTaskParsing, DumpportsOffOnVariableFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpportsoff(fname);\n"
              "    $dumpportson(fname);\n"
              "  end\n"
              "endmodule\n"));
}

// §21.7.3.2 negative: the task call requires a parenthesized argument; a
// filename butted against the task name without parentheses does not parse.
TEST(IoSystemTaskParsing, DumpportsoffUnparenthesizedFilenameRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  initial $dumpportsoff \"ports.vcd\";\n"
              "endmodule\n"));
}

// §21.7.3.2 negative: the same unparenthesized-filename form is rejected for
// the resume task too.
TEST(IoSystemTaskParsing, DumpportsonUnparenthesizedFilenameRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  initial $dumpportson \"ports.vcd\";\n"
              "endmodule\n"));
}

}  // namespace
