#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// Keywords and operators referenced literally by the BNF of §A.6.6
// (conditional_statement, unique_priority, cond_predicate, cond_pattern).

// unique_priority ::= unique | unique0 | priority
TEST(ConditionalStmtKeywordLexing, UniqueKeyword) {
  auto r = LexOne("unique");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUnique);
}

TEST(ConditionalStmtKeywordLexing, Unique0Keyword) {
  auto r = LexOne("unique0");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUnique0);
}

TEST(ConditionalStmtKeywordLexing, PriorityKeyword) {
  auto r = LexOne("priority");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPriority);
}

// conditional_statement keywords: if / else
TEST(ConditionalStmtKeywordLexing, IfKeyword) {
  auto r = LexOne("if");
  EXPECT_EQ(r.token.kind, TokenKind::kKwIf);
}

TEST(ConditionalStmtKeywordLexing, ElseKeyword) {
  auto r = LexOne("else");
  EXPECT_EQ(r.token.kind, TokenKind::kKwElse);
}

// cond_pattern ::= expression matches pattern
TEST(ConditionalStmtKeywordLexing, MatchesKeyword) {
  auto r = LexOne("matches");
  EXPECT_EQ(r.token.kind, TokenKind::kKwMatches);
}

// cond_predicate uses the &&& separator.
TEST(ConditionalStmtOperatorLexing, TripleAmp) {
  auto r = LexOne("&&&");
  EXPECT_EQ(r.token.kind, TokenKind::kAmpAmpAmp);
}

}  // namespace
