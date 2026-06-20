#include <gtest/gtest.h>

#include "fixture_preprocessor.h"
#include "helpers_begin_keywords_token_kind.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

TEST(KeywordVersionPreprocessing, BeginKeywords1364_1995_EmitsCorrectMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-1995\"\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer13641995);
}

TEST(KeywordVersionPreprocessing, BeginKeywords1364_1995_LexerSwitchesVersion) {
  ExpectBeginKeywordsTokenKind("1364-1995", "logic", TokenKind::kIdentifier);
}

TEST(KeywordVersionPreprocessing, BeginKeywords1364_1995_ModuleStaysKeyword) {
  ExpectBeginKeywordsTokenKind("1364-1995", "module", TokenKind::kKwModule);
}

}  // namespace
