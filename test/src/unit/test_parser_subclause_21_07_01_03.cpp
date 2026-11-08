#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumpOffOnExampleSequence) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    #10  $dumpvars;\n"
              "    #200 $dumpoff;\n"
              "    #800 $dumpon;\n"
              "    #900 $dumpoff;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpOffOnAsSoleStatement) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial #5 $dumpoff;\n"
              "  initial #9 $dumpon;\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpOffOnInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic clk;\n"
              "  always @(posedge clk) begin\n"
              "    $dumpoff;\n"
              "    $dumpon;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpOffOnInTaskBody) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  task pause_dump;\n"
              "    $dumpoff;\n"
              "  endtask\n"
              "  task resume_dump;\n"
              "    $dumpon;\n"
              "  endtask\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpOffMissingSemicolonRejected) {
  auto result = Parse(
      "module t;\n"
      "  initial begin\n"
      "    $dumpoff\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(result.diags, "expected ';', got 'end'", 4, "12.3"));
}

}  // namespace
