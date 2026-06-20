#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, WritememhCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememh(\"out.hex\", mem);\n"
              "endmodule\n"));
}

// §21.5 (Syntax 21-13): the production carries optional start_addr and
// finish_addr arguments after the memory name. The four-argument form must
// parse as well as the bare filename/memory form above.
TEST(IoSystemTaskParsing, WritememWithStartAndFinishAddresses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememh(\"out.hex\", mem, 16, 31);\n"
              "endmodule\n"));
}

}  // namespace
