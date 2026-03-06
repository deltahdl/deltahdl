#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §A.9.2 — one_line_comment: // comment_text \n

TEST(LexerA92, OneLineCommentStripped) {
  auto tokens = Lex("a // comment\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA92, OneLineCommentAtEof) {
  auto tokens = Lex("a // comment at eof");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(LexerA92, EmptyOneLineComment) {
  auto tokens = Lex("a //\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA92, OneLineCommentOnly) {
  auto tokens = Lex("// entire input is comment");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexerA92, ConsecutiveOneLineComments) {
  auto tokens = Lex("// line 1\n// line 2\na");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].text, "a");
}

TEST(LexerA92, OneLineCommentWithSpecialChars) {
  auto tokens = Lex("a // !@#$%^&*(){}[]|<>?\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

// §A.9.2 — block_comment: /* comment_text */

TEST(LexerA92, BlockCommentStripped) {
  auto tokens = Lex("a /* comment */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA92, EmptyBlockComment) {
  auto tokens = Lex("a /**/ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA92, MultiLineBlockComment) {
  auto tokens = Lex("a /* line1\nline2\nline3 */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA92, BlockCommentOnly) {
  auto tokens = Lex("/* only a comment */");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexerA92, StarsInsideBlockComment) {
  auto tokens = Lex("a /* ** stars ** */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA92, SlashesInsideBlockComment) {
  auto tokens = Lex("a /* // not a line comment */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

// §A.9.2 — block comments do not nest

TEST(LexerA92, BlockCommentsDoNotNest) {
  auto tokens = Lex("a /* outer /* inner */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

// §A.9.2 — unterminated block comment is an error

TEST(LexerA92, UnterminatedBlockCommentError) {
  auto [tokens, errors] = LexWithDiag("a /* unterminated");
  EXPECT_TRUE(errors);
}

// §A.9.2 — // has no special meaning in block comment, /* */ has none in line comment

TEST(LexerA92, LineCommentTokenInsideBlockComment) {
  auto tokens = Lex("a /* // still block */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA92, BlockCommentTokensInsideLineComment) {
  auto tokens = Lex("a // /* not a block */ still line\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

// §A.9.2 — comment as token separator

TEST(LexerA92, BlockCommentSeparatesKeywords) {
  auto tokens = Lex("module /* sep */ m;");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "m");
}

TEST(LexerA92, LineCommentSeparatesKeywords) {
  auto tokens = Lex("module // comment\nm;");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

// §A.9.2 — line tracking through comments

TEST(LexerA92, LineCommentAdvancesLineNumber) {
  auto [tokens, errors] = LexWithDiag("a\n// comment\nb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.line, 3u);
}

TEST(LexerA92, MultiLineBlockCommentAdvancesLineNumber) {
  auto [tokens, errors] = LexWithDiag("a\n/* \n \n */\nb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.line, 5u);
}

}  // namespace
