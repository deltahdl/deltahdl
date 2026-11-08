#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumpportsoffCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsoff(\"ports.vcd\");\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsonCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportson(\"ports.vcd\");\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsOffOnNoFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpportsoff;\n"
              "    $dumpportson;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsOffOnEmptyParenForms) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpportsoff();\n"
              "    $dumpportson();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsOffOnVariableFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpportsoff(fname);\n"
              "    $dumpportson(fname);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsoffUnparenthesizedFilenameRejected) {
  auto result = Parse(
      "module t;\n"
      "  initial $dumpportsoff \"ports.vcd\";\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(result.diags, "expected ';', got string literal", 2,
                            "12.3"));
}

TEST(IoSystemTaskParsing, DumpportsonUnparenthesizedFilenameRejected) {
  auto result = Parse(
      "module t;\n"
      "  initial $dumpportson \"ports.vcd\";\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(result.diags, "expected ';', got string literal", 2,
                            "12.3"));
}

}  // namespace
