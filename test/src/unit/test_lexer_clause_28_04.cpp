// §28.4

#include <gtest/gtest.h>
#include "fixture_lexer.h"

using namespace delta;

static const GateKeywordEntry kGateKeywords[] = {
    {"and", TokenKind::kKwAnd},
    {"nand", TokenKind::kKwNand},
    {"or", TokenKind::kKwOr},
    {"nor", TokenKind::kKwNor},
    {"xor", TokenKind::kKwXor},
    {"xnor", TokenKind::kKwXnor},
    {"buf", TokenKind::kKwBuf},
    {"not", TokenKind::kKwNot},
    {"bufif0", TokenKind::kKwBufif0},
    {"bufif1", TokenKind::kKwBufif1},
    {"notif0", TokenKind::kKwNotif0},
    {"notif1", TokenKind::kKwNotif1},
    {"nmos", TokenKind::kKwNmos},
    {"pmos", TokenKind::kKwPmos},
    {"rnmos", TokenKind::kKwRnmos},
    {"rpmos", TokenKind::kKwRpmos},
    {"cmos", TokenKind::kKwCmos},
    {"rcmos", TokenKind::kKwRcmos},
    {"tran", TokenKind::kKwTran},
    {"rtran", TokenKind::kKwRtran},
    {"tranif0", TokenKind::kKwTranif0},
    {"tranif1", TokenKind::kKwTranif1},
    {"rtranif0", TokenKind::kKwRtranif0},
    {"rtranif1", TokenKind::kKwRtranif1},
    {"pullup", TokenKind::kKwPullup},
    {"pulldown", TokenKind::kKwPulldown},
};

namespace {

TEST(NInputGateLexing, NamedAndGateTokenSequence) {
  auto tokens = Lex("and g1(y, a, b);");
  ASSERT_GE(tokens.size(), 8u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAnd);
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

TEST(NInputGateLexing, UnnamedOrGateTokenSequence) {
  auto tokens = Lex("or (out, a, b);");
  ASSERT_GE(tokens.size(), 8u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwOr);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

}  // namespace
