#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumplimitCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpfile(\"out.vcd\");\n"
              "    $dumplimit(1000000);\n"
              "    $dumpvars;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumplimitAsSoleStatement) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial #5 $dumplimit(4096);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumplimitInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic clk;\n"
              "  always @(posedge clk) begin\n"
              "    $dumplimit(4096);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumplimitInTaskBody) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  task cap;\n"
              "    $dumplimit(4096);\n"
              "  endtask\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumplimitParameterFilesize) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  parameter LIMIT = 200;\n"
              "  initial $dumplimit(LIMIT);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumplimitExpressionFilesize) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumplimit(2 * 512);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumplimitMissingSemicolonRejected) {
  auto result = Parse(
      "module t;\n"
      "  initial begin\n"
      "    $dumplimit(200)\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(result.diags, "expected ';', got 'end'", 4, "12.3"));
}

}  // namespace
