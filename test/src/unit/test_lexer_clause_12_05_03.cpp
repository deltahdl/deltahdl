#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §12.5.3 (N1): the lexer recognizes the three case-qualifier keywords that
// may precede `case`, `casez`, or `casex`.

TEST(CaseQualifierLexing, PriorityKeyword) {
  auto r = LexOne("priority");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPriority);
  EXPECT_EQ(r.token.text, "priority");
}

TEST(CaseQualifierLexing, UniqueKeyword) {
  auto r = LexOne("unique");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUnique);
  EXPECT_EQ(r.token.text, "unique");
}

TEST(CaseQualifierLexing, Unique0Keyword) {
  auto r = LexOne("unique0");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUnique0);
  EXPECT_EQ(r.token.text, "unique0");
}

TEST(CaseQualifierLexing, QualifierBeforeCaseTokenStream) {
  auto tokens = Lex("unique case (x)");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwUnique);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwCase);
}

TEST(CaseQualifierLexing, PriorityBeforeCasezTokenStream) {
  auto tokens = Lex("priority casez (x)");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwPriority);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwCasez);
}

TEST(CaseQualifierLexing, Unique0BeforeCasexTokenStream) {
  auto tokens = Lex("unique0 casex (x)");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwUnique0);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwCasex);
}

}  // namespace
