// §28.9

#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// Each CMOS switch keyword must map to its own token kind so the parser can
// distinguish full-strength from resistive variants.
TEST(CmosSwitchLexing, CmosKeyword) {
  auto tokens = Lex("cmos");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwCmos);
}

TEST(CmosSwitchLexing, RcmosKeyword) {
  auto tokens = Lex("rcmos");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwRcmos);
}

TEST(CmosSwitchLexing, CmosInstantiationTokenSequence) {
  auto tokens = Lex("cmos c1(out, data, nctrl, pctrl);");
  ASSERT_GE(tokens.size(), 12u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwCmos);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[6].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[7].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[8].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[9].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[10].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[11].kind, TokenKind::kSemicolon);
}

TEST(CmosSwitchLexing, RcmosInstantiationTokenSequence) {
  auto tokens = Lex("rcmos r1(out, data, nctrl, pctrl);");
  ASSERT_GE(tokens.size(), 12u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwRcmos);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

}  // namespace
