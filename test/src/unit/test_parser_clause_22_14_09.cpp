#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, BeginKeywords1800_2017) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2017\"\n"
                              "module t;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(CompilerDirectiveParsing, BeginKeywordsWithModuleContent) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2017\"\n"
                              "module t;\n"
                              "  logic [7:0] data;\n"
                              "  initial data = 8'hFF;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(CompilerDirectiveParsing, BeginKeywords1800_2023) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2023\"\n"
                              "module t;\n"
                              "  logic [7:0] data;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

}  // namespace
