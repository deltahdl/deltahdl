

#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(GateDelayLexing, NandWithDelayTokenSequence) {
  auto tokens = Lex("nand #5 g1(out, a, b);");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwNand);
  EXPECT_EQ(tokens[1].kind, TokenKind::kHash);
}

}  // namespace
