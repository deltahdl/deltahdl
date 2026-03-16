#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ConfigKeywordLexing, ConfigKeyword) {
  auto r = LexOne("config");
  EXPECT_EQ(r.token.kind, TokenKind::kKwConfig);
}

TEST(ConfigKeywordLexing, EndconfigKeyword) {
  auto r = LexOne("endconfig");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndconfig);
}

TEST(ConfigKeywordLexing, DesignKeyword) {
  auto r = LexOne("design");
  EXPECT_EQ(r.token.kind, TokenKind::kKwDesign);
}

TEST(ConfigKeywordLexing, LiblistKeyword) {
  auto r = LexOne("liblist");
  EXPECT_EQ(r.token.kind, TokenKind::kKwLiblist);
}

TEST(ConfigKeywordLexing, UseKeyword) {
  auto r = LexOne("use");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUse);
}

TEST(ConfigKeywordLexing, InstanceKeyword) {
  auto r = LexOne("instance");
  EXPECT_EQ(r.token.kind, TokenKind::kKwInstance);
}

TEST(ConfigKeywordLexing, DefaultKeyword) {
  auto r = LexOne("default");
  EXPECT_EQ(r.token.kind, TokenKind::kKwDefault);
}

TEST(ConfigKeywordLexing, CellKeyword) {
  auto r = LexOne("cell");
  EXPECT_EQ(r.token.kind, TokenKind::kKwCell);
}

TEST(ConfigKeywordLexing, ConfigKeywordSequence) {
  auto tokens = Lex("config endconfig design liblist");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwConfig);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndconfig);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwDesign);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwLiblist);
}

TEST(ConfigKeywordLexing, KeywordsNotIdentifiers) {
  auto tokens = Lex("config cfg1");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwConfig);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

}  // namespace
