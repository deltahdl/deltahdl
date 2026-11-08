#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(SystemCallLexing, NameStopsAtOpeningParen) {
  auto tokens = Lex("$system(\"ls\")");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$system");
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStringLiteral);
}

}  // namespace
