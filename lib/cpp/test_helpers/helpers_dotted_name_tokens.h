#pragma once

#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

// Lexes a three-component dotted name "<a>.<b>.<c>" and asserts the resulting
// token stream is identifier/dot/identifier/dot/identifier with the expected
// identifier texts.
inline void ExpectThreeComponentDottedNameTokens(const std::string& a,
                                                 const std::string& b,
                                                 const std::string& c) {
  auto tokens = Lex(a + "." + b + "." + c);
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, a);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, b);
  EXPECT_EQ(tokens[3].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].text, c);
}
