#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §6.9.2: vectored and scalared are the advisory keywords for vector net
// declarations. As keywords they shall be lexed to their reserved token kinds
// rather than to ordinary identifiers.

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
