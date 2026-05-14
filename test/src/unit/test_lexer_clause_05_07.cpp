#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §5.7.1: whitespace is permitted between the size and the apostrophe and
// between the apostrophe and the base specifier — a main-text rule that
// the §A.8.7 BNF does not itself express. The lexer's enforcement of the
// stricter rule (no whitespace between the apostrophe and base letter)
// surfaces here as the apostrophe breaking the token.
TEST(NumberLexing, WhitespaceBetweenApostropheAndBase) {
  auto tokens = Lex("8' hFF ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "8");
}

}  // namespace
