

#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_gate_instantiation_tokens.h"

using namespace delta;

namespace {

TEST(BufNotLexing, BufKeyword) {
  auto tokens = Lex("buf");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwBuf);
}

TEST(BufNotLexing, NotKeyword) {
  auto tokens = Lex("not");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwNot);
}

TEST(BufNotLexing, NamedBufGateTokenSequence) {
  auto tokens = Lex("buf b1(out, in);");
  ExpectNamedGateInstantiation(tokens, TokenKind::kKwBuf, 2);
}

}  // namespace
