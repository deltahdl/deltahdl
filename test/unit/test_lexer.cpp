#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

static std::vector<Token> lex(const std::string& src) {
  static SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  return lexer.LexAll();
}

TEST(Lexer, EmptyInput) {
  auto tokens = lex("");
  ASSERT_EQ(tokens.size(), 1);
  EXPECT_TRUE(tokens[0].IsEof());
}

TEST(Lexer, Keywords) {
  auto tokens = lex("module endmodule");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
  EXPECT_TRUE(tokens[2].IsEof());
}

TEST(Lexer, Identifiers) {
  auto tokens = lex("foo bar_123 _baz");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "foo");
  EXPECT_EQ(tokens[1].text, "bar_123");
  EXPECT_EQ(tokens[2].text, "_baz");
}

TEST(Lexer, IntegerLiterals) {
  auto tokens = lex("42 8'hFF 4'b1010");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "42");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].text, "8'hFF");
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].text, "4'b1010");
}

TEST(Lexer, StringLiterals) {
  auto tokens = lex("\"Hello, World!\"");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"Hello, World!\"");
}

TEST(Lexer, SystemIdentifiers) {
  auto tokens = lex("$display $finish");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
  EXPECT_EQ(tokens[1].text, "$finish");
}

TEST(Lexer, Operators) {
  auto tokens = lex("+ - * / == != <= >= << >> && ||");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[3].kind, TokenKind::kSlash);
  EXPECT_EQ(tokens[4].kind, TokenKind::kEqEq);
  EXPECT_EQ(tokens[5].kind, TokenKind::kBangEq);
  EXPECT_EQ(tokens[6].kind, TokenKind::kLtEq);
  EXPECT_EQ(tokens[7].kind, TokenKind::kGtEq);
  EXPECT_EQ(tokens[8].kind, TokenKind::kLtLt);
  EXPECT_EQ(tokens[9].kind, TokenKind::kGtGt);
  EXPECT_EQ(tokens[10].kind, TokenKind::kAmpAmp);
  EXPECT_EQ(tokens[11].kind, TokenKind::kPipePipe);
}

TEST(Lexer, Punctuation) {
  auto tokens = lex("( ) [ ] { } ; , . :");
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLBracket);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRBracket);
  EXPECT_EQ(tokens[4].kind, TokenKind::kLBrace);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRBrace);
  EXPECT_EQ(tokens[6].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[7].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[8].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[9].kind, TokenKind::kColon);
}

TEST(Lexer, SkipsComments) {
  auto tokens = lex("a // comment\nb /* block */ c");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].text, "c");
}

TEST(Lexer, HelloSv) {
  auto tokens = lex(
      "module hello;\n  initial $display(\"Hello, DeltaHDL!\");\nendmodule\n");
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "hello");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwInitial);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[4].text, "$display");
}

TEST(Lexer, RealLiteralFixed) {
  auto tokens = lex("3.14");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "3.14");
}

TEST(Lexer, RealLiteralExponent) {
  auto tokens = lex("1e10");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "1e10");
}

TEST(Lexer, RealLiteralFixedExponent) {
  auto tokens = lex("2.5e3");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "2.5e3");
}

TEST(Lexer, TimeLiteral) {
  auto tokens = lex("100ns");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(tokens[0].text, "100ns");
}

TEST(Lexer, TimeLiteralMs) {
  auto tokens = lex("10ms");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(tokens[0].text, "10ms");
}

TEST(Lexer, TimeLiteralRealBase) {
  auto tokens = lex("1.5us");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(tokens[0].text, "1.5us");
}

TEST(Lexer, SourceLocations) {
  auto tokens = lex("a\nb c");
  EXPECT_EQ(tokens[0].loc.line, 1);
  EXPECT_EQ(tokens[0].loc.column, 1);
  EXPECT_EQ(tokens[1].loc.line, 2);
  EXPECT_EQ(tokens[1].loc.column, 1);
  EXPECT_EQ(tokens[2].loc.line, 2);
  EXPECT_EQ(tokens[2].loc.column, 3);
}
