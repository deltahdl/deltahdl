// §21.4: Loading memory array data from a file

#include "fixture_parser.h"

using namespace delta;

namespace {

// ============================================================================
// Additional coverage -- Memory load/dump tasks from 21.1 overview
// ============================================================================
TEST(ParserSection21, ReadmemhBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemh(\"data.hex\", mem);\n"
              "endmodule\n"));
}

TEST(ParserSection21, ReadmemhWithAddresses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemh(\"data.hex\", mem, 0, 127);\n"
              "endmodule\n"));
}

TEST(ParserSection21, ReadmembBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemb(\"data.bin\", mem);\n"
              "endmodule\n"));
}

TEST(ParserSection21, ReadmembWithAddresses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemb(\"data.bin\", mem, 16, 31);\n"
              "endmodule\n"));
}

}  // namespace
