#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(SystemNameLexing, NameLexesAsSystemIdentifier) {
  auto r = LexOne("$display");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$display");
}

TEST(SystemNameLexing, BareDollarIsNotSystemIdentifier) {
  auto r = LexOne("$;");
  EXPECT_EQ(r.token.kind, TokenKind::kDollar);
  EXPECT_NE(r.token.kind, TokenKind::kSystemIdentifier);
}

TEST(SystemNameLexing, BareDollarAtEndOfInput) {
  auto r = LexOne("$");
  EXPECT_EQ(r.token.kind, TokenKind::kDollar);
  EXPECT_NE(r.token.kind, TokenKind::kSystemIdentifier);
}

TEST(SystemNameLexing, DigitFirstSystemIdentifier) {
  auto r = LexOne("$12step");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$12step");
}

TEST(SystemNameLexing, UnderscoreFirstSystemIdentifier) {
  auto r = LexOne("$_reset");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$_reset");
}

TEST(SystemNameLexing, EmbeddedDollarSystemIdentifier) {
  auto r = LexOne("$test$plusargs");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$test$plusargs");
}

TEST(SystemNameLexing, DollarFollowedByWhitespaceIsNotSystemIdentifier) {
  auto tokens = Lex("$ display ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
  EXPECT_NE(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "display");
}

TEST(SystemNameLexing, EscapedNameIsNotSystemIdentifier) {
  auto r = LexOne("\\$display ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_NE(r.token.kind, TokenKind::kSystemIdentifier);
}

TEST(SystemNameLexing, EscapedSystemTfIdentifierIsRejected) {
  auto diags = LexDiagnostics("\\$display ");
  EXPECT_TRUE(ReportedError(
      diags, "'$display' cannot be written as an escaped identifier", 1,
      "5.6.3"));
}

TEST(SystemNameLexing, EscapedSystemTaskEnableIsRejectedOnItsLine) {
  auto diags = LexDiagnostics(
      "module t;\n"
      "  initial \\$display (\"x\");\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      diags, "'$display' cannot be written as an escaped identifier", 2,
      "5.6.3"));
}

TEST(SystemNameLexing, EscapedNameThatIsNoSystemTfIdentifierReportsNothing) {
  EXPECT_TRUE(LexDiagnostics("\\$display-x ").empty());
  EXPECT_TRUE(LexDiagnostics("\\display ").empty());
  EXPECT_TRUE(LexDiagnostics("$display ").empty());
}

TEST(SystemNameLexing, ANameOfAnyLengthLexesAsOneSystemIdentifier) {
  std::string id = "$" + std::string(2000, 'a');
  id += " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text.size(), 2001u);
}

TEST(SystemNameLexing, EscapedNameThatNoSystemNameSpellsIsAccepted) {
  EXPECT_TRUE(LexDiagnostics("\\$a+b ").empty());
  auto tokens = Lex("\\$a+b ");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "$a+b");
}

TEST(SystemNameLexing, EscapedSystemNameWithUnderscoreAndDollarIsRejected) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("\\$my$task_1 "),
                            "cannot be written as an escaped identifier", 1,
                            "5.6.3"));
}

}  // namespace
