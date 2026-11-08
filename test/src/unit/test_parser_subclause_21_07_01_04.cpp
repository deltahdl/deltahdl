#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumpallNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpvars;\n"
              "    #50 $dumpall;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpallAsSoleStatement) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial #5 $dumpall;\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpallInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic clk;\n"
              "  always @(posedge clk) begin\n"
              "    $dumpall;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpallInTaskBody) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  task snapshot;\n"
              "    $dumpall;\n"
              "  endtask\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpallMissingSemicolonRejected) {
  auto result = Parse(
      "module t;\n"
      "  initial begin\n"
      "    $dumpall\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(result.diags, "expected ';', got 'end'", 4, "12.3"));
}

}  // namespace
