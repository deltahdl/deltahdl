#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(PlaSystemTaskLexing, AsyncAndArrayIsOneSystemIdentifier) {
  auto r = LexOne("$async$and$array ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$async$and$array");
}

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
