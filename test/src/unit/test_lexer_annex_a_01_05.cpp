#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(ConfigKeywordLexing, ConfigKeyword) {
  EXPECT_EQ(LexOne("config").token.kind, TokenKind::kKwConfig);
}

TEST(ConfigKeywordLexing, EndconfigKeyword) {
  EXPECT_EQ(LexOne("endconfig").token.kind, TokenKind::kKwEndconfig);
}

TEST(ConfigKeywordLexing, DesignKeyword) {
  EXPECT_EQ(LexOne("design").token.kind, TokenKind::kKwDesign);
}

TEST(ConfigKeywordLexing, LiblistKeyword) {
  EXPECT_EQ(LexOne("liblist").token.kind, TokenKind::kKwLiblist);
}

TEST(ConfigKeywordLexing, UseKeyword) {
  EXPECT_EQ(LexOne("use").token.kind, TokenKind::kKwUse);
}

TEST(ConfigKeywordLexing, InstanceKeyword) {
  EXPECT_EQ(LexOne("instance").token.kind, TokenKind::kKwInstance);
}

TEST(ConfigKeywordLexing, CellKeyword) {
  EXPECT_EQ(LexOne("cell").token.kind, TokenKind::kKwCell);
}

TEST(ConfigKeywordLexing, KeywordsAreNotIdentifiers) {
  auto tokens = Lex("config cfg1");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwConfig);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

}  // namespace
