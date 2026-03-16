#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "fixture_preprocessor.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

TEST(KeywordVersionPreprocessing, BeginKeywords1800_2017_EmitsCorrectMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1800-2017\"\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002017);
}

TEST(KeywordVersionPreprocessing, BeginKeywords1800_2023_EmitsCorrectMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1800-2023\"\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002023);
}

TEST(CompilerDirectiveParsing, BeginKeywordsModuleNamePreserved) {
  auto r = ParseWithPreprocessor(
      "`begin_keywords \"1800-2017\"\n"
      "module bar;\n"
      "  logic x;\n"
      "endmodule\n"
      "`end_keywords\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "bar");
}

}  // namespace
