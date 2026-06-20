#include <gtest/gtest.h>

#include "fixture_preprocessor.h"
#include "helpers_begin_keywords_token_kind.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

TEST(KeywordVersionPreprocessing, BeginKeywords1364_2001_EmitsCorrectMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2001\"\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer13642001);
}

TEST(KeywordVersionPreprocessing, BeginKeywords1364_2001_LogicIsIdentifier) {
  ExpectBeginKeywordsTokenKind("1364-2001", "logic", TokenKind::kIdentifier);
}

TEST(KeywordVersionPreprocessing, BeginKeywords1364_2001_GenerateIsKeyword) {
  ExpectBeginKeywordsTokenKind("1364-2001", "generate", TokenKind::kKwGenerate);
}

}  // namespace
