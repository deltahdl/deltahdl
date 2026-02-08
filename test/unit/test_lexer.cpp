#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

static std::vector<Token> lex(const std::string& src) {
  static SourceManager mgr;
  auto fid = mgr.add_file("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.file_content(fid), fid, diag);
  return lexer.lex_all();
}

TEST(Lexer, EmptyInput) {
  auto tokens = lex("");
  ASSERT_EQ(tokens.size(), 1);
  EXPECT_TRUE(tokens[0].is_eof());
}

TEST(Lexer, Keywords) {
  auto tokens = lex("module endmodule");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::KwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::KwEndmodule);
  EXPECT_TRUE(tokens[2].is_eof());
}

TEST(Lexer, Identifiers) {
  auto tokens = lex("foo bar_123 _baz");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::Identifier);
  EXPECT_EQ(tokens[0].text, "foo");
  EXPECT_EQ(tokens[1].text, "bar_123");
  EXPECT_EQ(tokens[2].text, "_baz");
}

TEST(Lexer, IntegerLiterals) {
  auto tokens = lex("42 8'hFF 4'b1010");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::IntLiteral);
  EXPECT_EQ(tokens[0].text, "42");
  EXPECT_EQ(tokens[1].kind, TokenKind::IntLiteral);
  EXPECT_EQ(tokens[1].text, "8'hFF");
  EXPECT_EQ(tokens[2].kind, TokenKind::IntLiteral);
  EXPECT_EQ(tokens[2].text, "4'b1010");
}

TEST(Lexer, StringLiterals) {
  auto tokens = lex("\"Hello, World!\"");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::StringLiteral);
  EXPECT_EQ(tokens[0].text, "\"Hello, World!\"");
}

TEST(Lexer, SystemIdentifiers) {
  auto tokens = lex("$display $finish");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::SystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
  EXPECT_EQ(tokens[1].text, "$finish");
}

TEST(Lexer, Operators) {
  auto tokens = lex("+ - * / == != <= >= << >> && ||");
  EXPECT_EQ(tokens[0].kind, TokenKind::Plus);
  EXPECT_EQ(tokens[1].kind, TokenKind::Minus);
  EXPECT_EQ(tokens[2].kind, TokenKind::Star);
  EXPECT_EQ(tokens[3].kind, TokenKind::Slash);
  EXPECT_EQ(tokens[4].kind, TokenKind::EqEq);
  EXPECT_EQ(tokens[5].kind, TokenKind::BangEq);
  EXPECT_EQ(tokens[6].kind, TokenKind::LtEq);
  EXPECT_EQ(tokens[7].kind, TokenKind::GtEq);
  EXPECT_EQ(tokens[8].kind, TokenKind::LtLt);
  EXPECT_EQ(tokens[9].kind, TokenKind::GtGt);
  EXPECT_EQ(tokens[10].kind, TokenKind::AmpAmp);
  EXPECT_EQ(tokens[11].kind, TokenKind::PipePipe);
}

TEST(Lexer, Punctuation) {
  auto tokens = lex("( ) [ ] { } ; , . :");
  EXPECT_EQ(tokens[0].kind, TokenKind::LParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::RParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::LBracket);
  EXPECT_EQ(tokens[3].kind, TokenKind::RBracket);
  EXPECT_EQ(tokens[4].kind, TokenKind::LBrace);
  EXPECT_EQ(tokens[5].kind, TokenKind::RBrace);
  EXPECT_EQ(tokens[6].kind, TokenKind::Semicolon);
  EXPECT_EQ(tokens[7].kind, TokenKind::Comma);
  EXPECT_EQ(tokens[8].kind, TokenKind::Dot);
  EXPECT_EQ(tokens[9].kind, TokenKind::Colon);
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
  EXPECT_EQ(tokens[0].kind, TokenKind::KwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::Identifier);
  EXPECT_EQ(tokens[1].text, "hello");
  EXPECT_EQ(tokens[2].kind, TokenKind::Semicolon);
  EXPECT_EQ(tokens[3].kind, TokenKind::KwInitial);
  EXPECT_EQ(tokens[4].kind, TokenKind::SystemIdentifier);
  EXPECT_EQ(tokens[4].text, "$display");
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
