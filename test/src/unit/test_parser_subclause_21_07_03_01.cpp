#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumpportsCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpports(t, \"ports.vcd\");\n"
              "endmodule\n"));
}

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

TEST(IoSystemTaskParsing, DumpportsNullScopeLeadingComma) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpports(, \"ports.vcd\");\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsMultipleScopes) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpports(a, b, \"ports.vcd\");\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsHierarchicalScopePath) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpports(c1.g1, \"ports.vcd\");\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsVariableFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpports(, fname);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsMissingArgumentSeparatorRejected) {
  auto result = Parse(
      "module t;\n"
      "  initial $dumpports(a \"ports.vcd\");\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(result.diags, "expected ')', got string literal", 2,
                            "13.5"));
}

}  // namespace
