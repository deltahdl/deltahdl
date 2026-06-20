#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(SequenceDeclarationLexing, SequenceKeywordsRoundTrip) {
  auto tokens = Lex("sequence endsequence");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwSequence);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndsequence);
}

TEST(SequenceDeclarationLexing, FormalTypeKeywordsRoundTrip) {
  auto tokens = Lex("untyped local");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwUntyped);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwLocal);
}

TEST(SequenceDeclarationLexing, PortDirectionKeywordsRoundTrip) {
  auto tokens = Lex("input inout output");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwInput);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwInout);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwOutput);
}

}  // namespace
