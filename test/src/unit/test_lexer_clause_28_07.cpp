

#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_gate_instantiation_tokens.h"

using namespace delta;

namespace {

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
  ExpectNamedGateInstantiation(tokens, TokenKind::kKwNmos, 3);
}

}  // namespace
