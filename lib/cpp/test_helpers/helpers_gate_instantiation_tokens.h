#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <vector>

#include "fixture_lexer.h"

using namespace delta;

// Verifies the token sequence for a named gate / switch / UDP instantiation of
// the form  `head inst(p0, p1, ...);`  with `num_ports` identifier ports.
// `head` is the leading token kind (a gate keyword such as TokenKind::kKwAnd,
// or TokenKind::kIdentifier for a UDP instance).
inline void ExpectNamedGateInstantiation(const std::vector<Token>& tokens,
                                         TokenKind head,
                                         std::size_t num_ports) {
  std::size_t total = 2 * num_ports + 4;
  ASSERT_GE(tokens.size(), total);
  EXPECT_EQ(tokens[0].kind, head);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  std::size_t idx = 3;
  for (std::size_t p = 0; p < num_ports; ++p) {
    EXPECT_EQ(tokens[idx++].kind, TokenKind::kIdentifier);
    if (p + 1 < num_ports) {
      EXPECT_EQ(tokens[idx++].kind, TokenKind::kComma);
    }
  }
  EXPECT_EQ(tokens[idx++].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[idx++].kind, TokenKind::kSemicolon);
}
