#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(LetKeywordLexing, LetDeclarationKeyword) {
  auto r = LexOne("let");
  EXPECT_EQ(r.token.kind, TokenKind::kKwLet);
  EXPECT_EQ(r.token.text, "let");
}

TEST(LetKeywordLexing, LetFormalTypeUntypedKeyword) {
  auto r = LexOne("untyped");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUntyped);
  EXPECT_EQ(r.token.text, "untyped");
}

}  // namespace
