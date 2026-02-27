#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

// --- §11.4.13: Set membership operator (tolerance) ---

TEST(LexerCh110413, ToleranceOperators) {
  // §11.4.13: +/- (absolute tolerance) and +%- (relative tolerance).
  auto tokens = Lex("+/- +%-");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlusSlashMinus);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlusPercentMinus);
}
