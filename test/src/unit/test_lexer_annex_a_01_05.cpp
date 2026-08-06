// Lexer coverage for the keyword terminals introduced by LRM Annex A, A.1.5
// "Configuration source text": config, endconfig, design, liblist, use,
// instance, and cell. (The 'default' terminal also appears in this subclause's
// grammar but predates it, so its keyword recognition is owned elsewhere —
// test_lexer_subclause_33_04_01.cpp, which also carries the §5.6
// case-sensitivity and maximal-munch rules that decide whether a spelling is
// one of these keywords at all.) Each test confirms the spelling is lexed as
// its reserved-word token rather than a plain identifier. Syntax 33-4 restates
// this same production, so these tests stand for both.
#include "fixture_lexer.h"

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

// A reserved word is distinguished from an identifier that merely follows it.
TEST(ConfigKeywordLexing, KeywordsAreNotIdentifiers) {
  auto tokens = Lex("config cfg1");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwConfig);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

}  // namespace
