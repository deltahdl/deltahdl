#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §20.16, Table 20-12: a PLA modeling system task name embeds dollar signs
// between its array_type, logic, and format components. The lexer treats those
// embedded dollars as part of a single system identifier token rather than
// splitting the name.
TEST(PlaSystemTaskLexing, AsyncAndArrayIsOneSystemIdentifier) {
  auto r = LexOne("$async$and$array ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$async$and$array");
}

// §20.16: the name is followed by its argument list; the lexer stops the system
// identifier at the opening parenthesis, leaving the call punctuation intact.
TEST(PlaSystemTaskLexing, NameStopsAtOpeningParen) {
  auto tokens = Lex("$async$and$plane(mem");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$async$and$plane");
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "mem");
}

}  // namespace
