#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LogicValuesLexer, LogicKeywordTokenizes) {
  auto tokens = Lex("logic");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwLogic);
  EXPECT_EQ(tokens[0].text, "logic");
}

TEST(LogicValuesLexer, LongerWordStartingWithLogicIsIdentifier) {
  auto tokens = Lex("logical");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "logical");
}

TEST(LogicValuesLexer, KeywordMatchIsCaseSensitive) {
  // §6.3.1 names the basic 4-state type with the exact keyword "logic".
  // Keyword recognition is case-sensitive, so a capitalized spelling is an
  // ordinary identifier rather than the type keyword.
  auto tokens = Lex("Logic");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "Logic");
}

}  // namespace
