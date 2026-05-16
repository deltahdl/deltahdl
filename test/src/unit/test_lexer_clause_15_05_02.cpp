#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §15.5.2: The wait syntax is "@ hierarchical_event_identifier;" — the
// lexer must produce the @ operator token (shared with §9.4.2's event
// control operator) so the parser can recognize the wait form.
TEST(NamedEventWaitLexer, AtOperatorTokenizes) {
  auto r = LexOne("@");
  EXPECT_EQ(r.token.kind, TokenKind::kAt);
}

// §15.5.2: "@ev" is the bare wait form. The lexer must tokenize it as
// kAt followed by an identifier so the parser can bind to the named event.
TEST(NamedEventWaitLexer, BareWaitFormTokenizes) {
  auto tokens = Lex("@ev");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "ev");
}

// §15.5.2: "@(ev);" is the parenthesized wait form (uses the @
// hierarchical_event_identifier production through the event_control
// alternative shared with §9.4.2).
TEST(NamedEventWaitLexer, ParenthesizedWaitFormTokenizes) {
  auto tokens = Lex("@(ev);");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "ev");
  EXPECT_EQ(tokens[3].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

// §15.5.2: The wait identifier may be hierarchical (an event reached
// through dotted module-instance path). The lexer must produce the
// identifier-dot-identifier sequence the parser needs to build a
// hierarchical_event_identifier.
TEST(NamedEventWaitLexer, HierarchicalWaitFormTokenizes) {
  auto tokens = Lex("@c1.ev;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "c1");
  EXPECT_EQ(tokens[2].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].text, "ev");
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

// §15.5.2 builds on §15.5's trigger operator "->". The wait/trigger
// ordering rule ("the waiting process shall execute the @ statement
// before the triggering process executes the trigger operator, ->")
// requires both tokens. Verify they coexist in a single source span.
TEST(NamedEventWaitLexer, WaitAndTriggerOperatorsTokenize) {
  auto tokens = Lex("@ev; ->ev;");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "ev");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kArrow);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].text, "ev");
  EXPECT_EQ(tokens[5].kind, TokenKind::kSemicolon);
}

}  // namespace
