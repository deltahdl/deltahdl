#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, BeginKeywords1364_2001_noconfig) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001-noconfig\"\n"
                              "module t;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(CompilerDirectiveParsing,
     BeginKeywords1364_2001Noconfig_ConfigAsIdentifier) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001-noconfig\"\n"
                              "module t;\n"
                              "  integer config;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(CompilerDirectiveParsing,
     BeginKeywords1364_2001Noconfig_LibraryAsIdentifier) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001-noconfig\"\n"
                              "module t;\n"
                              "  integer library;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

}  // namespace
