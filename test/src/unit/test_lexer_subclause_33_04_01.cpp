#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(ConfigKeywordLexing, ConfigStartKeyword) {
  auto r = LexOne("config ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwConfig);
}

TEST(ConfigKeywordLexing, DefaultKeyword) {
  auto r = LexOne("default ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwDefault);
}

TEST(ConfigKeywordLexing, KeywordsAreCaseSensitive) {
  auto r = LexOne("Config ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "Config");
}

TEST(ConfigKeywordLexing, KeywordPrefixLexesAsSingleIdentifier) {
  auto r = LexOne("designs ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "designs");
}

}  // namespace
