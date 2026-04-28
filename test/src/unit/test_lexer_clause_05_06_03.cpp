#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(SystemNameLexing, BasicSystemIdentifier) {
  auto r = LexOne("$display ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$display");
}

TEST(SystemNameLexing, SystemFinish) {
  auto r = LexOne("$finish ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$finish");
}

TEST(SystemNameLexing, SystemTime) {
  auto r = LexOne("$time ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$time");
}

TEST(SystemNameLexing, EmbeddedDollar) {
  auto tokens = Lex("$test$plusargs $value$plusargs");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$test$plusargs");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].text, "$value$plusargs");
}

TEST(SystemNameLexing, BareDollarNotSystemId) {
  auto r = LexOne("$ ");
  EXPECT_EQ(r.token.kind, TokenKind::kDollar);
}

TEST(SystemNameLexing, DigitsInName) {
  auto r = LexOne("$sformat ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$sformat");
}

TEST(SystemNameLexing, UnderscoreInName) {
  auto r = LexOne("$read_mem ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$read_mem");
}

TEST(SystemNameLexing, MaxLengthOk) {
  std::string id = "$" + std::string(1023, 'a');
  id += " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
}

TEST(SystemNameLexing, DigitAsFirstChar) {
  auto r = LexOne("$0 ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$0");
}

TEST(SystemNameLexing, EmbeddedDollarFollowedByDigit) {
  auto r = LexOne("$test$0plusargs ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$test$0plusargs");
}

TEST(SystemNameLexing, TrailingDollar) {
  auto tokens = Lex("$test$ ;");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$test$");
}

TEST(SystemNameLexing, StartsWithUnderscore) {
  auto r = LexOne("$_my_task ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$_my_task");
}

TEST(SystemNameLexing, DollarFollowedByNewlineNotSystemId) {
  auto tokens = Lex("$\n");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

TEST(SystemNameLexing, SingleCharSuffix) {
  auto r = LexOne("$a ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$a");
}

TEST(SystemNameLexing, UppercaseOnly) {
  auto r = LexOne("$ABC ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$ABC");
}

TEST(SystemNameLexing, DollarFollowedByTabNotSystemId) {
  auto tokens = Lex("$\t");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

TEST(SystemNameLexing, DollarAtEofNotSystemId) {
  auto tokens = Lex("$");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

// §5.6.3 footnote 55: "The $ character in a system_tf_identifier shall not be
// followed by white_space." §5.3 lists the carriage return as white_space, so
// `$\r` must terminate the leading `$` as a kDollar (queue-dimension/last-
// index operator), not begin a system_tf_identifier.
TEST(SystemNameLexing, DollarFollowedByCarriageReturnNotSystemId) {
  auto tokens = Lex("$\r");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

// §5.6.3 footnote 55: same rule for the form-feed character, which §5.3
// includes in white_space.
TEST(SystemNameLexing, DollarFollowedByFormFeedNotSystemId) {
  auto tokens = Lex("$\f");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

TEST(SystemNameLexing, ExceedsMaxLength) {
  std::string id = "$" + std::string(1024, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

TEST(SystemNameLexing, MultipleInStream) {
  auto tokens = Lex("$display $finish $time");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].text, "$finish");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[2].text, "$time");
}

// §5.6.3 (footnote 55): "A system_tf_identifier shall not be escaped." The
// escaped form `\$display ` must therefore lex as an escaped (user-defined)
// identifier per §5.6.1 — never as the system identifier `$display` — so a
// name colliding with a simulator task cannot silently bind to the simulator's
// implementation.
TEST(SystemNameLexing, EscapedDollarIsNotSystemId) {
  auto r = LexOne("\\$display ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_NE(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$display");
}

}  // namespace
