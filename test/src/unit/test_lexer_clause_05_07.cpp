#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(NumberLexing, WhitespaceBetweenApostropheAndBase) {
  auto tokens = Lex("8' hFF ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "8");
}

}
