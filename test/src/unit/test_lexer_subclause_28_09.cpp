

#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_gate_instantiation_tokens.h"

using namespace delta;

namespace {

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
  ExpectNamedGateInstantiation(tokens, TokenKind::kKwCmos, 4);
}

TEST(CmosSwitchLexing, RcmosInstantiationTokenSequence) {
  auto tokens = Lex("rcmos r1(out, data, nctrl, pctrl);");
  ASSERT_GE(tokens.size(), 12u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwRcmos);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

}  // namespace
