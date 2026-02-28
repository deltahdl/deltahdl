// §21.3.4.4: Reading binary data

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, FreadBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  reg [31:0] data;\n"
              "  initial begin\n"
              "    fd = $fopen(\"bin.dat\", \"rb\");\n"
              "    $fread(data, fd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection21, FreadWithStartCount) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial begin\n"
              "    fd = $fopen(\"bin.dat\", \"rb\");\n"
              "    $fread(mem, fd, 0, 256);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
