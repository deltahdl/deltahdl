#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

TEST_F(ApiParseTest, ReadmemhSystemCall) {
  auto* unit = Parse(R"(
    module m;
      logic [7:0] mem [0:255];
      initial $readmemh("data.hex", mem);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

}
