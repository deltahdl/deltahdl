#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// A.2.12 let_declaration begins with the `let` keyword. The lexer must
// recognize it as a distinct token rather than an ordinary identifier.
TEST(LetKeywordLexing, LetKeyword) {
  auto r = LexOne("let");
  EXPECT_EQ(r.token.kind, TokenKind::kKwLet);
  EXPECT_EQ(r.token.text, "let");
}

// A.2.12 let_formal_type ::= data_type_or_implicit | untyped. The `untyped`
// alternative is spelled with a reserved keyword.
TEST(LetKeywordLexing, UntypedKeyword) {
  auto r = LexOne("untyped");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUntyped);
  EXPECT_EQ(r.token.text, "untyped");
}

// The let_identifier that follows the keyword is a separate identifier token.
TEST(LetKeywordLexing, LetThenIdentifier) {
  auto tokens = Lex("let mux");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwLet);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "mux");
}

// `untyped` keeps its keyword identity inside a port list context.
TEST(LetKeywordLexing, UntypedThenFormal) {
  auto tokens = Lex("untyped a");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwUntyped);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "a");
}

}  // namespace
