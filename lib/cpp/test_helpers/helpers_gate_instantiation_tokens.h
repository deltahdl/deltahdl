#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <vector>

#include "lexer/token.h"

using namespace delta;

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
