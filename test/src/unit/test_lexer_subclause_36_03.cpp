#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

// §36.3 — User-defined system task and system function names.
//
// The own text of 36.3 defines the lexical form of a user-defined system
// task/function name. It is a lexer-stage rule, carried by
// Lexer::LexSystemIdentifier in src/lexer/lexer.cpp. The four enumerated
// claims:
//   S1: the first character of the name is the dollar sign ($).
//   S2: the remaining characters are letters, digits, the underscore (_),
//       or the dollar sign ($).
//   S3: the name is case sensitive (upper/lower considered unique).
//   S4: the name can be any size, and all characters are significant. §5.6's
//       identifier length cap does not reach it, §5.6.3 having handed a
//       user-defined system task or system function name to Clause 36.
//
// Descendant subclauses (36.3.1 callback registry, 36.3.2 overriding built-ins)
// are out of scope here.

namespace {

// S1: a name beginning with '$' (followed by a word character) is lexed as a
// system identifier whose text starts with the dollar sign.
TEST(SystemTfNameLexing, FirstCharacterIsDollar) {
  auto r = LexOne("$display ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$display");
  ASSERT_FALSE(r.token.text.empty());
  EXPECT_EQ(r.token.text.front(), '$');
}

// S1 boundary: a bare '$' not followed by a name character is the dollar
// operator, not a system identifier — the system-identifier path is taken
// only for a '$' that begins a name.
TEST(SystemTfNameLexing, BareDollarIsNotSystemIdentifier) {
  auto r = LexOne("$ ");
  EXPECT_NE(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.kind, TokenKind::kDollar);
}

// S2: the characters after '$' may be letters, digits, underscores, and
// further dollar signs; all are consumed into the one name.
TEST(SystemTfNameLexing, RemainingCharactersAreWordCharsAndDollar) {
  auto r = LexOne("$a_B9$z ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$a_B9$z");
}

// S2: a digit may immediately follow the leading '$'.
TEST(SystemTfNameLexing, DigitMayFollowDollar) {
  auto r = LexOne("$123abc ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$123abc");
}

// S2: an underscore may immediately follow the leading '$' — the dispatch
// still routes the '$' into a single system identifier rather than splitting
// it from the following name.
TEST(SystemTfNameLexing, UnderscoreMayFollowDollar) {
  auto r = LexOne("$_foo ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$_foo");
}

// S2: a second '$' may immediately follow the leading '$'; both dollars and the
// trailing word characters form one system identifier.
TEST(SystemTfNameLexing, DollarMayFollowDollar) {
  auto r = LexOne("$$foo ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$$foo");
}

// S2: a character outside {letter, digit, _, $} terminates the name; it is not
// absorbed into the system identifier.
TEST(SystemTfNameLexing, NonWordCharacterEndsName) {
  auto tokens = Lex("$foo.bar");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$foo");
  EXPECT_NE(tokens[1].kind, TokenKind::kSystemIdentifier);
}

// S3: system task/function names are case sensitive — names differing only in
// case lex to distinct tokens whose text preserves the original case, and they
// are never folded to a keyword.
TEST(SystemTfNameLexing, CaseSensitiveDistinctNames) {
  auto tokens = Lex("$Foo $foo $FOO");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$Foo");
  EXPECT_EQ(tokens[1].text, "$foo");
  EXPECT_EQ(tokens[2].text, "$FOO");
  EXPECT_NE(tokens[0].text, tokens[1].text);
  EXPECT_NE(tokens[1].text, tokens[2].text);
}

// S4: a long name is consumed in full, with no truncation.
TEST(SystemTfNameLexing, LongNameKeptInFull) {
  std::string name = "$";
  name.append(500, 'a');
  auto r = LexOne(name + " ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, name);
  EXPECT_EQ(r.token.text.size(), name.size());
}

// S4: all characters are significant — two long names differing only at a late
// position lex to different texts (no significance limit collapses them).
TEST(SystemTfNameLexing, AllCharactersAreSignificant) {
  std::string prefix = "$";
  prefix.append(300, 'x');
  auto a = LexOne(prefix + "1 ");
  auto b = LexOne(prefix + "2 ");
  EXPECT_EQ(a.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(b.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_NE(a.token.text, b.token.text);
}

// S4: 1024 characters is where §5.6 lets an implementation stop reading an
// identifier -- "the limit shall be at least 1024 characters" -- so a name of
// exactly that length is the last one both readings of the rule accept.
TEST(SystemTfNameLexing, AName1024CharactersLongIsAccepted) {
  std::string name = "$";
  name.append(1023, 'a');
  auto [tokens, errors] = LexWithDiag(name + " ");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, name);
  EXPECT_EQ(tokens[0].text.size(), 1024u);
}

// S4 is where the two part. §5.6 caps an identifier, but an identifier there is
// "either a simple identifier or an escaped identifier" and a simple
// identifier's first character "shall not be a digit or $", so a system task or
// system function name is neither; §5.6.3 hands its rules to Clause 36
// ("Additional user-defined system tasks and system functions can be defined
// using the PLI, as described in Clause 36"), and this is the rule Clause 36
// gives: "The name can be any size, and all characters are significant." So a
// name past that cap is lexed whole, with no diagnostic.
TEST(SystemTfNameLexing, ANameLongerThan1024CharactersIsStillOneName) {
  std::string name = "$";
  name.append(2000, 'a');
  auto [tokens, errors] = LexWithDiag(name + " ");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, name);
  EXPECT_EQ(tokens[0].text.size(), 2001u);
}

}  // namespace
