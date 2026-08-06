#include "fixture_lexer.h"

using namespace delta;

namespace {

// 18.5.3: a distribution is written with the "dist" operator keyword
// (expression_or_dist ::= expression [ dist { dist_list } ]). The lexer must
// classify "dist" as a keyword token so the parser can match the dist form of
// a constraint expression.
TEST(ConstraintDistLexing, DistKeywordRecognised) {
  auto r = LexOne("dist");
  EXPECT_EQ(r.token.kind, TokenKind::kKwDist);
}

// 18.5.3: a dist_item may be the "default" specification ("default :/ expr").
// The lexer must classify "default" as a keyword token so the parser can
// recognise the default item within a dist_list.
TEST(ConstraintDistLexing, DefaultKeywordRecognised) {
  auto r = LexOne("default");
  EXPECT_EQ(r.token.kind, TokenKind::kKwDefault);
}

}  // namespace
