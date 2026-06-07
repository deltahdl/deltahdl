#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumpportsCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpports(t, \"ports.vcd\");\n"
              "endmodule\n"));
}

// §21.7.3.1: with no arguments both $dumpports; and $dumpports(); are accepted.
TEST(IoSystemTaskParsing, DumpportsNoArguments) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpports;\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpports();\n"
              "endmodule\n"));
}

// §21.7.3.1: when the scope_list (first argument) is null, a leading comma
// precedes the filename, so $dumpports(, filename); is a valid form.
TEST(IoSystemTaskParsing, DumpportsNullScopeLeadingComma) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpports(, \"ports.vcd\");\n"
              "endmodule\n"));
}

// §21.7.3.1: a scope_list may list more than one module, separated by commas,
// ahead of the filename argument.
TEST(IoSystemTaskParsing, DumpportsMultipleScopes) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpports(a, b, \"ports.vcd\");\n"
              "endmodule\n"));
}

}
