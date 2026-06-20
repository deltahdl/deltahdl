#pragma once

#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

// Lexes a replication-style assignment pattern of the form '{ N { inner } } and
// asserts the canonical six leading token kinds it produces:
//   kApostropheLBrace IntLiteral LBrace IntLiteral RBrace RBrace
// `src` must be a source whose first six tokens follow that shape (e.g.
// "'{3{4}}" or "'{4{8'hAB}}").
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
