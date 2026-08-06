#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// Syntax 20-17: system_call ::= $system ( [ "terminal_command_line" ] ). The
// callee name $system is lexed as a single system identifier token, and the
// lexer stops that token at the opening parenthesis of the argument list.
TEST(SystemCallLexing, NameStopsAtOpeningParen) {
  auto tokens = Lex("$system(\"ls\")");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$system");
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStringLiteral);
}

}  // namespace
