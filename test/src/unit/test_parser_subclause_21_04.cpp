#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

// Syntax 21-12: the finish_addr is nested inside the start_addr option, so a
// three-argument call (filename, memory_name, start_addr) is a distinct,
// legal form of the production.
TEST(IoSystemTaskParsing, ReadmemhWithStartAddrOnly) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemh(\"data.hex\", mem, 16);\n"
              "endmodule\n"));
}

// §21.4: memory_name may name its lowest dimension with slice syntax (see
// 7.4.5). The task call still parses as a legal load_memory_tasks production.
TEST(IoSystemTaskParsing, ReadmemhWithSliceMemoryName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemh(\"data.hex\", mem[16:31]);\n"
              "endmodule\n"));
}

// §21.4: memory_name may be a partially indexed multidimensional unpacked array
// that resolves to a lesser-dimensioned array; the higher dimension is indexed.
TEST(IoSystemTaskParsing, ReadmemhWithPartiallyIndexedMemoryName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:3][0:255];\n"
              "  initial $readmemh(\"data.hex\", mem[1]);\n"
              "endmodule\n"));
}

}  // namespace
