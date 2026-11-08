#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumpflushNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpvars;\n"
              "    $dumpflush;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpflushAsSoleStatement) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial #5 $dumpflush;\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpflushInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic clk;\n"
              "  always @(posedge clk) begin\n"
              "    $dumpflush;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpflushInTaskBody) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  task sync_dump;\n"
              "    $dumpflush;\n"
              "  endtask\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpflushMissingSemicolonRejected) {
  auto result = Parse(
      "module t;\n"
      "  initial begin\n"
      "    $dumpflush\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(result.diags, "expected ';', got 'end'", 4, "12.3"));
}

}  // namespace
