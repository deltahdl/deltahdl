

#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_gate_instantiation_tokens.h"

using namespace delta;

namespace {

TEST(NInputGateLexing, NamedAndGateTokenSequence) {
  auto tokens = Lex("and g1(y, a, b);");
  ExpectNamedGateInstantiation(tokens, TokenKind::kKwAnd, 3);
}

TEST(NInputGateLexing, UnnamedOrGateTokenSequence) {
  auto tokens = Lex("or (out, a, b);");
  ASSERT_GE(tokens.size(), 8u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwOr);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(NInputGateLexing, NandKeyword) {
  auto tokens = Lex("nand");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwNand);
}

TEST(NInputGateLexing, NorKeyword) {
  auto tokens = Lex("nor");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwNor);
}

TEST(NInputGateLexing, XorKeyword) {
  auto tokens = Lex("xor");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwXor);
}

TEST(NInputGateLexing, XnorKeyword) {
  auto tokens = Lex("xnor");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwXnor);
}

}  // namespace
