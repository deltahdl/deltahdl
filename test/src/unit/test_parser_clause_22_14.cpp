#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection22, BeginKeywords1800_2023) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2023\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1800_2005) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2005\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywordsMultipleModules) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2012\"\n"
              "module m1;\n"
              "endmodule\n"
              "module m2;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

}
