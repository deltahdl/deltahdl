#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(DefparamLexer, DefparamKeywordToken) {
  auto tokens = Lex("defparam");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwDefparam);
}

TEST(DefparamLexer, DefparamStatementTokenSequence) {
  auto tokens = Lex("defparam u.X = 99;");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwDefparam);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "u");
  EXPECT_EQ(tokens[2].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].text, "X");
  EXPECT_EQ(tokens[4].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[6].kind, TokenKind::kSemicolon);
}

TEST(DefparamLexer, MultipleAssignmentsCommaToken) {
  auto tokens = Lex("defparam u.A = 1, u.B = 2;");
  bool saw_comma = false;
  for (const auto& tk : tokens) {
    if (tk.kind == TokenKind::kComma) {
      saw_comma = true;
      break;
    }
  }
  EXPECT_TRUE(saw_comma);
}

}  // namespace
