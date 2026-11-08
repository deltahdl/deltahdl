#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(ConstraintImplicationLexing, ArrowOperatorRecognised) {
  auto r = LexOne("->");
  EXPECT_EQ(r.token.kind, TokenKind::kArrow);
}

}  // namespace
