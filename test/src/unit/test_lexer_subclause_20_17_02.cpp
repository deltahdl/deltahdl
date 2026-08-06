#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// Syntax 20-18: stacktrace_call ::= $stacktrace. The callee name $stacktrace is
// lexed as a single system identifier token; unlike $system it takes no
// argument list, so the token stands on its own.
TEST(StacktraceCallLexing, NameIsOneSystemIdentifier) {
  auto tokens = Lex("$stacktrace;");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$stacktrace");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSemicolon);
}

// Syntax 20-18 negative form: without the leading $, the word stacktrace is an
// ordinary identifier, not the system task/function name the production names.
TEST(StacktraceCallLexing, NameWithoutDollarIsOrdinaryIdentifier) {
  auto tokens = Lex("stacktrace;");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_NE(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "stacktrace");
}

}  // namespace
