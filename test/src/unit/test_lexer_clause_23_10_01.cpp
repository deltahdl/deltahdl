#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

// §23.10.1 defparam statement: a defparam statement begins with the keyword
// `defparam`. The keyword shall lex to TokenKind::kKwDefparam.

namespace {

TEST(DefparamLexer, DefparamKeywordToken) {
  auto tokens = Lex("defparam");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwDefparam);
}

// §23.10.1: the canonical `defparam u.X = 99;` sequence shall lex as the
// defparam keyword followed by a hierarchical identifier path, an equals
// sign, a literal, and a semicolon — the token sequence the parser relies on
// to build a defparam statement.
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

// §23.10.1: the comma-separated `list_of_defparam_assignments` BNF expects
// the comma to lex as its own token between two assignments.
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
