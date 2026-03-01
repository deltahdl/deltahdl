// §21.5: Writing memory array data to a file

#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

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

namespace {

TEST_F(ApiParseTest, WritememhSystemCall) {
  auto* unit = Parse(R"(
    module m;
      logic [7:0] mem [0:255];
      initial $writememh("data.hex", mem);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST(ParserSection21, WritememhCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememh(\"out.hex\", mem);\n"
              "endmodule\n"));
}

TEST(ParserSection21, WritemembCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememb(\"out.bin\", mem);\n"
              "endmodule\n"));
}

}  // namespace
