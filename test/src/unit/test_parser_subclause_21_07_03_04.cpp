#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumpportslimitCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportslimit(500000);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportslimitCallWithFileName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportslimit(500000, \"ports.vcd\");\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportslimitExpressionFilesizeVariableFilename) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportslimit(2 * 250000, fname);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportslimitIdentifierFilesize) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportslimit(lim, \"ports.vcd\");\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportslimitNullFilesizeCommaFormParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportslimit(, \"ports.vcd\");\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportslimitUnparenthesizedFilesizeRejected) {
  auto result = Parse(
      "module t;\n"
      "  initial $dumpportslimit 500000;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(result.diags, "expected ';', got integer literal",
                            2, "12.3"));
}

}  // namespace
