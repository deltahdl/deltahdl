#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, BeginKeywords1364_1995) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-1995\"\n"
                              "module t;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(CompilerDirectiveParsing, BeginKeywords1364_1995_LogicAsIdentifier) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-1995\"\n"
                              "module t;\n"
                              "  reg [7:0] logic;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(CompilerDirectiveParsing, BeginKeywords1364_1995_ClassAsIdentifier) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-1995\"\n"
                              "module t;\n"
                              "  integer class;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

}  // namespace
