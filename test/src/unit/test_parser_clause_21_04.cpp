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

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

struct ParseResult40 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult40 Parse(const std::string& src) {
  ParseResult40 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
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

}  // namespace
