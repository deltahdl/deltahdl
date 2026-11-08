#pragma once

#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

inline void ExpectReplicationPatternTokens(const std::string& src) {
  auto tokens = Lex(src);
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLBrace);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRBrace);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRBrace);
}
