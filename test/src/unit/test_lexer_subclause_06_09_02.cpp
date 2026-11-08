#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(VectorNetAccessibilityLexing, VectoredIsKeyword) {
  auto r = LexOne("vectored");
  EXPECT_EQ(r.token.kind, TokenKind::kKwVectored);
  EXPECT_EQ(r.token.text, "vectored");
}

TEST(VectorNetAccessibilityLexing, ScalaredIsKeyword) {
  auto r = LexOne("scalared");
  EXPECT_EQ(r.token.kind, TokenKind::kKwScalared);
  EXPECT_EQ(r.token.text, "scalared");
}

}  // namespace
