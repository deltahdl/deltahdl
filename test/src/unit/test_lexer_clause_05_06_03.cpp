#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §5.6.3: a name following the `$` is recognized as a system task/function
// identifier token. This observes the recognition rule directly, independent of
// the §5.6 length-limit checks below. The lexer makes no task-vs-function
// distinction, so a single recognition case covers the rule at this stage.
TEST(SystemNameLexing, NameLexesAsSystemIdentifier) {
  auto r = LexOne("$display");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$display");
}

// §5.6.3 conditions the rule on a name *following* the `$`. When nothing
// name-like follows, the construct is not interpreted as a system
// task/function: the lexer emits a plain dollar token rather than a system
// identifier. This observes the negative branch of the recognition decision.
TEST(SystemNameLexing, BareDollarIsNotSystemIdentifier) {
  auto r = LexOne("$;");
  EXPECT_EQ(r.token.kind, TokenKind::kDollar);
  EXPECT_NE(r.token.kind, TokenKind::kSystemIdentifier);
}

// §5.6.3 recognition negative at the end-of-input boundary: a `$` that is the
// last character of the source has no following name at all, so it likewise
// yields a bare dollar rather than a system task/function identifier. This
// exercises the past-the-end lookahead path, distinct from the `$;` (non-word
// follows) and `$ ` (white space follows) negatives.
TEST(SystemNameLexing, BareDollarAtEndOfInput) {
  auto r = LexOne("$");
  EXPECT_EQ(r.token.kind, TokenKind::kDollar);
  EXPECT_NE(r.token.kind, TokenKind::kSystemIdentifier);
}

// §5.6.3 (Syntax 5-1 char class): the character after the `$` may be any of a
// letter, digit, underscore, or `$`. This case (and the two below) exercise the
// non-letter members of the first/continuation character class so the full
// admitted set is observed at the stage that owns the token rule. The letter
// member is covered by NameLexesAsSystemIdentifier above. See the
// §5.3-dependent negatives below for where the class stops applying.
TEST(SystemNameLexing, DigitFirstSystemIdentifier) {
  auto r = LexOne("$12step");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$12step");
}

// §5.6.3 char class, underscore member: a leading underscore after the `$` is
// admitted, so the whole `$_name` is a single system task/function identifier.
TEST(SystemNameLexing, UnderscoreFirstSystemIdentifier) {
  auto r = LexOne("$_reset");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$_reset");
}

// §5.6.3 char class, `$` member: `$` is admitted in the continuation, so an
// embedded dollar does not terminate the identifier — the lexer consumes the
// whole `$test$plusargs` as one system task/function identifier token rather
// than splitting it at the interior `$`.
TEST(SystemNameLexing, EmbeddedDollarSystemIdentifier) {
  auto r = LexOne("$test$plusargs");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$test$plusargs");
}

// §5.6.3 footnote 55 (rule 1): the `$` shall not be followed by white space.
// A `$` immediately followed by a §5.3 white-space character is therefore not
// the start of a system task/function name; the lexer emits a bare dollar and
// tokenizes the following name independently. This observes the white-space
// branch specifically, distinct from the generic non-word case ($;) above.
TEST(SystemNameLexing, DollarFollowedByWhitespaceIsNotSystemIdentifier) {
  auto tokens = Lex("$ display ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
  EXPECT_NE(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "display");
}

// §5.6.3 footnote 55 (rule 2): a system_tf_identifier shall not be escaped.
// A name introduced with the §5.6.1 escape backslash is an ordinary
// (user-defined) escaped identifier even when its spelling begins with `$`;
// it is not recognized as a system task/function name.
TEST(SystemNameLexing, EscapedNameIsNotSystemIdentifier) {
  auto r = LexOne("\\$display ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_NE(r.token.kind, TokenKind::kSystemIdentifier);
}

TEST(SystemNameLexing, MaxLengthOk) {
  std::string id = "$" + std::string(1023, 'a');
  id += " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
}

TEST(SystemNameLexing, ExceedsMaxLength) {
  std::string id = "$" + std::string(1024, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

}  // namespace
