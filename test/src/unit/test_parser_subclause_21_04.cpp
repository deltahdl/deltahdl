#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, ReadmemhBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemh(\"data.hex\", mem);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, ReadmemhWithAddresses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemh(\"data.hex\", mem, 0, 127);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, ReadmembBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemb(\"data.bin\", mem);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, ReadmembWithAddresses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemb(\"data.bin\", mem, 16, 31);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, ReadmemhWithStartAddrOnly) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemh(\"data.hex\", mem, 16);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, ReadmemhWithSliceMemoryName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemh(\"data.hex\", mem[16:31]);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, ReadmemhWithPartiallyIndexedMemoryName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:3][0:255];\n"
              "  initial $readmemh(\"data.hex\", mem[1]);\n"
              "endmodule\n"));
}

}  // namespace
