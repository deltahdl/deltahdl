#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(ConstraintIfElseLexing, IfKeywordRecognised) {
  auto r = LexOne("if");
  EXPECT_EQ(r.token.kind, TokenKind::kKwIf);
}

TEST(ConstraintIfElseLexing, ElseKeywordRecognised) {
  auto r = LexOne("else");
  EXPECT_EQ(r.token.kind, TokenKind::kKwElse);
}

}  // namespace
