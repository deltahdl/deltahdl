#include "fixture_lexer.h"

using namespace delta;

namespace {

// 18.5.5: implication is written with the implication operator "->". The lexer
// must recognize "->" as a single operator token so the parser can match the
// "expression -> constraint_set" form of a constraint expression.
TEST(ConstraintImplicationLexing, ArrowOperatorRecognised) {
  auto r = LexOne("->");
  EXPECT_EQ(r.token.kind, TokenKind::kArrow);
}

}  // namespace
