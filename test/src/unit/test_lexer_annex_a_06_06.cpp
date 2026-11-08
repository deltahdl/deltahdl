#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

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

TEST(ConditionalStmtKeywordLexing, IfKeyword) {
  auto r = LexOne("if");
  EXPECT_EQ(r.token.kind, TokenKind::kKwIf);
}

TEST(ConditionalStmtKeywordLexing, ElseKeyword) {
  auto r = LexOne("else");
  EXPECT_EQ(r.token.kind, TokenKind::kKwElse);
}

TEST(ConditionalStmtKeywordLexing, MatchesKeyword) {
  auto r = LexOne("matches");
  EXPECT_EQ(r.token.kind, TokenKind::kKwMatches);
}

TEST(ConditionalStmtOperatorLexing, TripleAmp) {
  auto r = LexOne("&&&");
  EXPECT_EQ(r.token.kind, TokenKind::kAmpAmpAmp);
}

}  // namespace
