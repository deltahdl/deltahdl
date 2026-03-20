// §28.3.1

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

TEST(GateKeywordLexing, AllTwentySixKeywords) {
  for (const auto& entry : kGateKeywords) {
    auto r = LexOne(entry.text);
    EXPECT_EQ(r.token.kind, entry.expected) << "keyword: " << entry.text;
  }
}

}  // namespace
