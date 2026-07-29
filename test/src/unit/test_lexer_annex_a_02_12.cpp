#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// A.2.12 let_declaration begins with the `let` keyword. The lexer must
// recognize it as a distinct token rather than an ordinary identifier.
// The clause 11.12 lexer file covers the prose side of the same keyword.
TEST(LetKeywordLexing, LetDeclarationKeyword) {
  auto r = LexOne("let");
  EXPECT_EQ(r.token.kind, TokenKind::kKwLet);
  EXPECT_EQ(r.token.text, "let");
}

// A.2.12 let_formal_type ::= data_type_or_implicit | untyped. The `untyped`
// alternative is spelled with a reserved keyword. The clause 11.12 lexer
// file covers the prose side of the same keyword.
TEST(LetKeywordLexing, LetFormalTypeUntypedKeyword) {
  auto r = LexOne("untyped");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUntyped);
  EXPECT_EQ(r.token.text, "untyped");
}

}  // namespace
