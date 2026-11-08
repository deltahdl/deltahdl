#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumpportsflushCallWithFileName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsflush(\"ports.vcd\");\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsflushEmptyParenCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsflush();\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsflushBareCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsflush;\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsflushVariableFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsflush(fname);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsflushExpressionFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsflush({stem, \".vcd\"});\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsflushInsideTaskBody) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  task do_flush;\n"
              "    $dumpportsflush(\"ports.vcd\");\n"
              "  endtask\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsflushUnparenthesizedFilenameRejected) {
  auto result = Parse(
      "module t;\n"
      "  initial $dumpportsflush \"ports.vcd\";\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(result.diags, "expected ';', got string literal", 2,
                            "12.3"));
}

}  // namespace
