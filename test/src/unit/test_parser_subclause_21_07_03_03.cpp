#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumpportsallCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsall(\"ports.vcd\");\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsallNoFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsall;\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsallEmptyParenForm) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsall();\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsallVariableFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsall(fname);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsallUnparenthesizedFilenameRejected) {
  auto result = Parse(
      "module t;\n"
      "  initial $dumpportsall \"ports.vcd\";\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(result.diags, "expected ';', got string literal", 2,
                            "12.3"));
}

}  // namespace
