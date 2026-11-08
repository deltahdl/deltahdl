#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(StacktraceCallLexing, NameIsOneSystemIdentifier) {
  auto tokens = Lex("$stacktrace;");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$stacktrace");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSemicolon);
}

TEST(StacktraceCallLexing, NameWithoutDollarIsOrdinaryIdentifier) {
  auto tokens = Lex("stacktrace;");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_NE(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "stacktrace");
}

}  // namespace
