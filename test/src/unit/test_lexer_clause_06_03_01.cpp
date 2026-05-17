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

TEST(LogicValuesLexer, LogicKeywordRecognizedInsideDeclaration) {
  auto tokens = Lex("logic [7:0] v;");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwLogic);
}

}
