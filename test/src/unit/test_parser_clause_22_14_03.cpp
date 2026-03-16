#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, BeginKeywords1364_2001) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001\"\n"
                              "module t;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(CompilerDirectiveParsing, BeginKeywords1364_2001_LogicAsIdentifier) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001\"\n"
                              "module t;\n"
                              "  wire logic;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(CompilerDirectiveParsing, BeginKeywords1364_2001_ClassAsIdentifier) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001\"\n"
                              "module t;\n"
                              "  integer class;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

}  // namespace
