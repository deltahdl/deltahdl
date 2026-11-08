#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, WritememhCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememh(\"out.hex\", mem);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, WritemembCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememb(\"out.bin\", mem);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, WritememWithStartAndFinishAddresses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememh(\"out.hex\", mem, 16, 31);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, WritemembWithStartAndFinishAddresses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememb(\"out.bin\", mem, 16, 31);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, WritememWithStartAddrOnly) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememh(\"out.hex\", mem, 16);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, WritememWithPartiallyIndexedMemoryName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:3][0:255];\n"
              "  initial $writememh(\"out.hex\", mem[1]);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, WritemembWithStartAddrOnly) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememb(\"out.bin\", mem, 16);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, WritememWithHierarchicalMemoryName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  sub u1();\n"
              "  initial $writememh(\"out.hex\", u1.mem);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, WritememWithSliceMemoryName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememh(\"out.hex\", mem[16:31]);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, WritememOperandsMayBeExpressions) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  parameter BASE = 16;\n"
              "  string fn;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememh(fn, mem, BASE, BASE + 15);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, WritememInAlwaysAndTaskPositions) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg clk;\n"
              "  reg [7:0] mem [0:255];\n"
              "  task dump;\n"
              "    $writememb(\"out.bin\", mem);\n"
              "  endtask\n"
              "  always @(posedge clk) $writememh(\"out.hex\", mem);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, UnterminatedWritememRejected) {
  auto result = Parse(
      "module t;\n"
      "  reg [7:0] mem [0:255];\n"
      "  initial $writememh(\"out.hex\", mem;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(result.diags, "expected ')', got ';'", 3, "13.5"));
}

}  // namespace
