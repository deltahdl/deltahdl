#include "fixture_lexer.h"

using namespace delta;

namespace {

// 18.5.6: an if-else constraint is introduced by the "if" keyword. The lexer
// must classify "if" as a keyword token so the parser can match the
// "if ( expression ) constraint_set [ else constraint_set ]" constraint form.
TEST(ConstraintIfElseLexing, IfKeywordRecognised) {
  auto r = LexOne("if");
  EXPECT_EQ(r.token.kind, TokenKind::kKwIf);
}

// 18.5.6: the optional alternative of an if-else constraint is introduced by
// the "else" keyword, which the lexer must classify as a keyword token.
TEST(ConstraintIfElseLexing, ElseKeywordRecognised) {
  auto r = LexOne("else");
  EXPECT_EQ(r.token.kind, TokenKind::kKwElse);
}

}  // namespace
