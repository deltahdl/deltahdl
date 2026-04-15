// §23.3.1

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(TopLevelModules, DollarRootLexesAsSystemIdentifier) {
  auto r = LexOne("$root ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$root");
}

TEST(TopLevelModules, DollarRootDotPathTokenSequence) {
  auto tokens = Lex("$root.A.B");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$root");
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "A");
  EXPECT_EQ(tokens[3].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].text, "B");
}

TEST(TopLevelModules, DollarRootAloneLexesSingleToken) {
  auto tokens = Lex("$root");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$root");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

}  // namespace
