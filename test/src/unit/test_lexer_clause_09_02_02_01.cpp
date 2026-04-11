#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(GeneralPurposeAlwaysLexing, AlwaysKeyword) {
  auto r = LexOne("always ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlways);
  EXPECT_EQ(r.token.text, "always");
}

TEST(GeneralPurposeAlwaysLexing, AlwaysPrefixIsIdentifier) {
  auto r = LexOne("always_xyz ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "always_xyz");
}

TEST(GeneralPurposeAlwaysLexing, UppercaseIsIdentifier) {
  auto r = LexOne("ALWAYS ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
}

TEST(GeneralPurposeAlwaysLexing, AlwaysFollowedByHash) {
  auto tokens = Lex("always #5");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAlways);
  EXPECT_EQ(tokens[1].kind, TokenKind::kHash);
}

}  // namespace
