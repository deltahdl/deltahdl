#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §21.7.3.3 (Syntax 21-23): the $dumpportsall task takes a single filename
// argument and parses as a generic system task call.
TEST(IoSystemTaskParsing, DumpportsallCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsall(\"ports.vcd\");\n"
              "endmodule\n"));
}

// §21.7.3.3: the filename argument is optional; the no-argument form
// checkpoints every file opened by $dumpports.
TEST(IoSystemTaskParsing, DumpportsallNoFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsall;\n"
              "endmodule\n"));
}

// §21.7.3.3: leaving the filename unspecified also admits the empty
// parenthesized call form.
TEST(IoSystemTaskParsing, DumpportsallEmptyParenForm) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsall();\n"
              "endmodule\n"));
}

// §21.7.3.3: the filename is an expression, so the task accepts an identifier
// (a string-typed or integral variable holding the name) instead of a literal.
TEST(IoSystemTaskParsing, DumpportsallVariableFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsall(fname);\n"
              "endmodule\n"));
}

// §21.7.3.3 negative: the task call requires a parenthesized argument; a
// filename butted against the task name without parentheses does not parse.
TEST(IoSystemTaskParsing, DumpportsallUnparenthesizedFilenameRejected) {
  auto result = Parse(
      "module t;\n"
      "  initial $dumpportsall \"ports.vcd\";\n"
      "endmodule\n");
  // §12.3 owns the semicolon that terminates a subroutine call statement, and
  // the unparenthesized filename is what stands where that semicolon must be.
  EXPECT_TRUE(ReportedError(result.diags, "expected ';', got string literal", 2,
                            "12.3"));
}

}  // namespace
