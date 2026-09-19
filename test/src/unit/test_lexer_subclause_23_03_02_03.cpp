
#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(ImplicitNamedPortConnectionLexing, NoParenthesesAfterImplicitPortName) {
  auto tokens = Lex("sub u0(.a, .b(x))");
  ASSERT_GE(tokens.size(), 12u);
  EXPECT_EQ(tokens[4].text, "a");
  EXPECT_EQ(tokens[5].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[7].text, "b");
  EXPECT_EQ(tokens[8].kind, TokenKind::kLParen);
}

}  // namespace
