#include <gtest/gtest.h>

#include "fixture_preprocessor.h"
#include "helpers_begin_keywords_token_kind.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

TEST(KeywordVersionPreprocessing, BeginKeywords1364_2005_EmitsCorrectMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2005\"\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer13642005);
}

TEST(KeywordVersionPreprocessing, BeginKeywords1364_2005_UwireIsKeyword) {
  ExpectBeginKeywordsTokenKind("1364-2005", "uwire", TokenKind::kKwUwire);
}

TEST(KeywordVersionPreprocessing, BeginKeywords1364_2005_LogicIsIdentifier) {
  ExpectBeginKeywordsTokenKind("1364-2005", "logic", TokenKind::kIdentifier);
}

}  // namespace
