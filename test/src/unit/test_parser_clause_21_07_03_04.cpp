#include "fixture_parser.h"

using namespace delta;

namespace {

// Syntax 21-24: the filesize-only form, where the limit covers every file
// opened by $dumpports.
TEST(IoSystemTaskParsing, DumpportslimitCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportslimit(500000);\n"
              "endmodule\n"));
}

// Syntax 21-24: the filesize-plus-filename form, naming the $dumpports output
// the limit applies to.
TEST(IoSystemTaskParsing, DumpportslimitCallWithFileName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportslimit(500000, \"ports.vcd\");\n"
              "endmodule\n"));
}

// Syntax 21-24: both arguments are expressions -- the filesize as an
// arithmetic expression and the filename as an identifier (a string-typed or
// integral variable holding the name) parse in their respective positions.
TEST(IoSystemTaskParsing, DumpportslimitExpressionFilesizeVariableFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportslimit(2 * 250000, fname);\n"
              "endmodule\n"));
}

// Syntax 21-24: the filesize position also admits a lone identifier, the form
// a parameter- or variable-held byte budget takes.
TEST(IoSystemTaskParsing, DumpportslimitIdentifierFilesize) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportslimit(lim, \"ports.vcd\");\n"
              "endmodule\n"));
}

// Syntax 21-24: a null first argument marked by a leading comma parses, the
// form that reaches the runtime's required-filesize check with only the
// filename supplied.
TEST(IoSystemTaskParsing, DumpportslimitNullFilesizeCommaFormParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportslimit(, \"ports.vcd\");\n"
              "endmodule\n"));
}

// Syntax 21-24 negative: the task call requires a parenthesized argument list;
// a filesize butted against the task name without parentheses does not parse.
TEST(IoSystemTaskParsing, DumpportslimitUnparenthesizedFilesizeRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  initial $dumpportslimit 500000;\n"
              "endmodule\n"));
}

}  // namespace
