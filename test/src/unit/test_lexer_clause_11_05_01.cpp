#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

// --- §11.5.1: Vector bit-select and part-select addressing ---

TEST(LexerCh11501, IndexedPartSelectOperators) {
  // §11.5.1: +: and -: for indexed part-selects.
  auto tokens = Lex("+: -:");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlusColon);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinusColon);
}
