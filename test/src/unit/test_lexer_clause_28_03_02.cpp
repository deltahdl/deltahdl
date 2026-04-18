// §28.3.2

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

TEST(GateStrengthLexing, DriveStrengthTokenSequence) {
  auto tokens = Lex("and (strong0, weak1) g1(y, a, b);");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAnd);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwStrong0);
  EXPECT_EQ(tokens[3].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[4].kind, TokenKind::kKwWeak1);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRParen);
}

// Every keyword listed as a valid strength0 must lex to its dedicated kind.
TEST(GateStrengthLexing, AllStrength0Keywords) {
  EXPECT_EQ(LexOne("supply0").token.kind, TokenKind::kKwSupply0);
  EXPECT_EQ(LexOne("strong0").token.kind, TokenKind::kKwStrong0);
  EXPECT_EQ(LexOne("pull0").token.kind, TokenKind::kKwPull0);
  EXPECT_EQ(LexOne("weak0").token.kind, TokenKind::kKwWeak0);
  EXPECT_EQ(LexOne("highz0").token.kind, TokenKind::kKwHighz0);
}

// Every keyword listed as a valid strength1 must lex to its dedicated kind.
TEST(GateStrengthLexing, AllStrength1Keywords) {
  EXPECT_EQ(LexOne("supply1").token.kind, TokenKind::kKwSupply1);
  EXPECT_EQ(LexOne("strong1").token.kind, TokenKind::kKwStrong1);
  EXPECT_EQ(LexOne("pull1").token.kind, TokenKind::kKwPull1);
  EXPECT_EQ(LexOne("weak1").token.kind, TokenKind::kKwWeak1);
  EXPECT_EQ(LexOne("highz1").token.kind, TokenKind::kKwHighz1);
}

}  // namespace
