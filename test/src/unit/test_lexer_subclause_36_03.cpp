#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(SystemTfNameLexing, FirstCharacterIsDollar) {
  auto r = LexOne("$display ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$display");
  ASSERT_FALSE(r.token.text.empty());
  EXPECT_EQ(r.token.text.front(), '$');
}

TEST(SystemTfNameLexing, BareDollarIsNotSystemIdentifier) {
  auto r = LexOne("$ ");
  EXPECT_NE(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.kind, TokenKind::kDollar);
}

TEST(SystemTfNameLexing, RemainingCharactersAreWordCharsAndDollar) {
  auto r = LexOne("$a_B9$z ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$a_B9$z");
}

TEST(SystemTfNameLexing, DigitMayFollowDollar) {
  auto r = LexOne("$123abc ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$123abc");
}

TEST(SystemTfNameLexing, UnderscoreMayFollowDollar) {
  auto r = LexOne("$_foo ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$_foo");
}

TEST(SystemTfNameLexing, DollarMayFollowDollar) {
  auto r = LexOne("$$foo ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$$foo");
}

TEST(SystemTfNameLexing, NonWordCharacterEndsName) {
  auto tokens = Lex("$foo.bar");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$foo");
  EXPECT_NE(tokens[1].kind, TokenKind::kSystemIdentifier);
}

TEST(SystemTfNameLexing, CaseSensitiveDistinctNames) {
  auto tokens = Lex("$Foo $foo $FOO");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$Foo");
  EXPECT_EQ(tokens[1].text, "$foo");
  EXPECT_EQ(tokens[2].text, "$FOO");
  EXPECT_NE(tokens[0].text, tokens[1].text);
  EXPECT_NE(tokens[1].text, tokens[2].text);
}

TEST(SystemTfNameLexing, LongNameKeptInFull) {
  std::string name = "$";
  name.append(500, 'a');
  auto r = LexOne(name + " ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, name);
  EXPECT_EQ(r.token.text.size(), name.size());
}

TEST(SystemTfNameLexing, AllCharactersAreSignificant) {
  std::string prefix = "$";
  prefix.append(300, 'x');
  auto a = LexOne(prefix + "1 ");
  auto b = LexOne(prefix + "2 ");
  EXPECT_EQ(a.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(b.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_NE(a.token.text, b.token.text);
}

TEST(SystemTfNameLexing, AName1024CharactersLongIsAccepted) {
  std::string name = "$";
  name.append(1023, 'a');
  auto [tokens, errors] = LexWithDiag(name + " ");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, name);
  EXPECT_EQ(tokens[0].text.size(), 1024u);
}

TEST(SystemTfNameLexing, ANameLongerThan1024CharactersIsStillOneName) {
  std::string name = "$";
  name.append(2000, 'a');
  auto [tokens, errors] = LexWithDiag(name + " ");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, name);
  EXPECT_EQ(tokens[0].text.size(), 2001u);
}

}  // namespace
