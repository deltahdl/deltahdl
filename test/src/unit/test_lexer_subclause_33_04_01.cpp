// Tests for IEEE 1800-2023 §33.4.1 "Basic configuration syntax" (Syntax 33-4).
// Recognition of the keyword terminals that Syntax 33-4 shares with the A.1.5
// "Configuration source text" production — endconfig, design, instance, cell,
// liblist and use — is covered by test_lexer_annex_a_01_05.cpp. Per §5.6.2 a
// keyword is a predefined nonescaped identifier, so its recognition does not
// depend on whether whitespace or the end of the source terminates it, and
// repeating those terminals here would restate that file's claims.
#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

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

// The config keyword terminals are reserved words spelled in lower case;
// a differently-cased spelling must lex as an ordinary identifier.
TEST(ConfigKeywordLexing, KeywordsAreCaseSensitive) {
  auto r = LexOne("Config ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "Config");
}

// A longer word that merely begins with a config keyword is a single
// identifier, not the keyword followed by a suffix (maximal munch).
TEST(ConfigKeywordLexing, KeywordPrefixLexesAsSingleIdentifier) {
  auto r = LexOne("designs ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "designs");
}

}  // namespace
