#include "fixture_lexer.h"

using namespace delta;

namespace {

// Integration robustness: the :: scope-resolution prefix tokenizes as
// identifier / kColonColon / identifier so the elaborator can apply §23.7.1.
TEST(ScopeResolutionPrefixLexing, TwoComponentPrefixTokens) {
  auto tokens = Lex("pkg::name");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "pkg");
  EXPECT_EQ(tokens[1].kind, TokenKind::kColonColon);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "name");
}

// Integration robustness: the scope-resolution operator is lexically distinct
// from the dotted-name operator, so §23.7.1's :: rule never sees a kDot.
TEST(ScopeResolutionPrefixLexing, PrefixTokensDistinctFromDot) {
  auto dot_tokens = Lex("a.b");
  auto scope_tokens = Lex("a::b");
  ASSERT_GE(dot_tokens.size(), 4u);
  ASSERT_GE(scope_tokens.size(), 4u);
  EXPECT_EQ(dot_tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(scope_tokens[1].kind, TokenKind::kColonColon);
}

}  // namespace
