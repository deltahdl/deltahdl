#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(FinalProcedureLexing, FinalKeyword) {
  auto r = LexOne("final ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwFinal);
  EXPECT_EQ(r.token.text, "final");
}

TEST(FinalProcedureLexing, FinalPrefixIsIdentifier) {
  auto r = LexOne("final_value ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "final_value");
}

TEST(FinalProcedureLexing, UppercaseIsIdentifier) {
  auto r = LexOne("FINAL ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
}

TEST(FinalProcedureLexing, FinalFollowedByStatement) {
  auto tokens = Lex("final x = 1;");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwFinal);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

TEST(FinalProcedureLexing, FinalFollowedByBegin) {
  auto tokens = Lex("final begin");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwFinal);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwBegin);
}

}  // namespace
