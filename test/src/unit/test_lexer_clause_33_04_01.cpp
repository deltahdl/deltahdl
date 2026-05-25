// Tests for IEEE 1800-2023 §33.4.1 "Basic configuration syntax" (Syntax 33-4).
// The config grammar uses several keyword terminals; these tests confirm the
// lexer emits the correct token kind for each terminal symbol of Syntax 33-4.
#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ConfigKeywordLexing, ConfigStartKeyword) {
  auto r = LexOne("config ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwConfig);
}

TEST(ConfigKeywordLexing, EndconfigKeyword) {
  auto r = LexOne("endconfig ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndconfig);
}

TEST(ConfigKeywordLexing, DesignKeyword) {
  auto r = LexOne("design ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwDesign);
}

TEST(ConfigKeywordLexing, DefaultKeyword) {
  auto r = LexOne("default ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwDefault);
}

TEST(ConfigKeywordLexing, InstanceKeyword) {
  auto r = LexOne("instance ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwInstance);
}

TEST(ConfigKeywordLexing, CellKeyword) {
  auto r = LexOne("cell ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwCell);
}

TEST(ConfigKeywordLexing, LiblistKeyword) {
  auto r = LexOne("liblist ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwLiblist);
}

TEST(ConfigKeywordLexing, UseKeyword) {
  auto r = LexOne("use ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUse);
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
