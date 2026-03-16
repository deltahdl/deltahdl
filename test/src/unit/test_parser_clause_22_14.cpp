#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(KeywordVersionParsing, BeginKeywords1800_2023) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2023\"\n"
                              "module t;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(KeywordVersionParsing, BeginKeywords1800_2005) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2005\"\n"
                              "module t;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(KeywordVersionParsing, BeginKeywordsMultipleModules) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2012\"\n"
                              "module m1;\n"
                              "endmodule\n"
                              "module m2;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(KeywordVersionParsing, NestedBeginKeywordsParses) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2012\"\n"
                              "`begin_keywords \"1364-2001\"\n"
                              "module t;\n"
                              "endmodule\n"
                              "`end_keywords\n"
                              "`end_keywords\n"));
}

TEST(KeywordVersionParsing, OldVersionIdentifierInExpression) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001\"\n"
                              "module t;\n"
                              "  wire logic;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

}  // namespace
