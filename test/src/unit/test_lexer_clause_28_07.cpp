// §28.7

#include <gtest/gtest.h>
#include "fixture_lexer.h"

using namespace delta;

namespace {

// Each MOS switch keyword must map to its own token kind so the parser can
// distinguish nmos from pmos and rnmos from rpmos.
TEST(MosSwitchLexing, NmosKeyword) {
  auto tokens = Lex("nmos");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwNmos);
}

TEST(MosSwitchLexing, PmosKeyword) {
  auto tokens = Lex("pmos");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwPmos);
}

TEST(MosSwitchLexing, RnmosKeyword) {
  auto tokens = Lex("rnmos");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwRnmos);
}

TEST(MosSwitchLexing, RpmosKeyword) {
  auto tokens = Lex("rpmos");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwRpmos);
}

TEST(MosSwitchLexing, NamedSwitchTokenSequence) {
  auto tokens = Lex("nmos n1(out, in, ctrl);");
  ASSERT_GE(tokens.size(), 10u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwNmos);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[6].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[7].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[8].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[9].kind, TokenKind::kSemicolon);
}

}  // namespace
