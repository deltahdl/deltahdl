#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §6.3.1 ¶4: "The name of the basic 4-state data type is logic." The lexer
// must recognize the bare word `logic` as the kKwLogic keyword token.
TEST(LogicValuesLexer, LogicKeywordTokenizes) {
  auto tokens = Lex("logic");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwLogic);
  EXPECT_EQ(tokens[0].text, "logic");
}

// §6.3.1 ¶4 edge case: a longer word that merely starts with "logic" must lex
// as an identifier, not as the kKwLogic keyword. Confirms the lexer matches
// the whole keyword, not just a prefix.
TEST(LogicValuesLexer, LongerWordStartingWithLogicIsIdentifier) {
  auto tokens = Lex("logical");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "logical");
}

// §6.3.1 ¶4: each occurrence of `logic` produces a kKwLogic token, so a
// declaration like `logic [7:0] v;` is built from a kKwLogic followed by the
// usual range/identifier tokens. Confirms the keyword is reusable per-token.
TEST(LogicValuesLexer, LogicKeywordRecognizedInsideDeclaration) {
  auto tokens = Lex("logic [7:0] v;");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwLogic);
}

}  // namespace
