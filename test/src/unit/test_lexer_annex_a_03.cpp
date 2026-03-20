// Non-LRM tests

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

TEST(GateKeywordLexing, PassSwitchTokenSequence) {
  auto tokens = Lex("tran (a, b);");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTran);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
}

TEST(GateKeywordLexing, MultipleGateKeywordsInSequence) {
  auto tokens = Lex("and nand or nor xor xnor");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAnd);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwNand);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwOr);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwNor);
  EXPECT_EQ(tokens[4].kind, TokenKind::kKwXor);
  EXPECT_EQ(tokens[5].kind, TokenKind::kKwXnor);
}

TEST(GateKeywordLexing, GateKeywordSubstringIsIdentifier) {
  auto r = LexOne("ands");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
}

TEST(GateKeywordLexing, GateKeywordPrefixIsIdentifier) {
  auto r = LexOne("tranif");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
}

TEST(GateKeywordLexing, StrengthInGateContextTokenSequence) {
  auto tokens = Lex("and (strong0, weak1) g1(y, a, b);");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAnd);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwStrong0);
  EXPECT_EQ(tokens[3].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[4].kind, TokenKind::kKwWeak1);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRParen);
}

}  // namespace
