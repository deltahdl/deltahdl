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

// §21.7.3.1: a scope_list entry may be a path name to a module using the
// period hierarchy separator.
TEST(IoSystemTaskParsing, DumpportsHierarchicalScopePath) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpports(c1.g1, \"ports.vcd\");\n"
              "endmodule\n"));
}

// §21.7.3.1: the filename is an expression, so it may be an identifier (a
// string-typed or integral variable holding the name) rather than a literal.
TEST(IoSystemTaskParsing, DumpportsVariableFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpports(, fname);\n"
              "endmodule\n"));
}

// §21.7.3.1 negative: the task's arguments are comma-separated, so a scope
// butted directly against the filename with no separator does not parse.
TEST(IoSystemTaskParsing, DumpportsMissingArgumentSeparatorRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  initial $dumpports(a \"ports.vcd\");\n"
              "endmodule\n"));
}

}  // namespace
