#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(EventControlLexing, AtToken) {
  auto r = LexOne("@");
  EXPECT_EQ(r.token.kind, TokenKind::kAt);
}

TEST(EventControlLexing, PosedgeKeyword) {
  auto r = LexOne("posedge");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPosedge);
}

TEST(EventControlLexing, NegedgeKeyword) {
  auto r = LexOne("negedge");
  EXPECT_EQ(r.token.kind, TokenKind::kKwNegedge);
}

TEST(EventControlLexing, EdgeKeyword) {
  auto r = LexOne("edge");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEdge);
}

TEST(EventControlLexing, AtFollowedByIdentifier) {
  auto tokens = Lex("@clk");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

TEST(EventControlLexing, AtFollowedByParenPosedge) {
  auto tokens = Lex("@(posedge clk)");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwPosedge);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
}

}  // namespace
