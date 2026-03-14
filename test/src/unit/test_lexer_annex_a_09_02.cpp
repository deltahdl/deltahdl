#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(CommentLexing, OneLineCommentStripped) {
  auto tokens = Lex("a // comment\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, OneLineCommentAtEof) {
  auto tokens = Lex("a // comment at eof");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(CommentLexing, EmptyOneLineComment) {
  auto tokens = Lex("a //\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, OneLineCommentOnly) {
  auto tokens = Lex("// entire input is comment");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(CommentLexing, ConsecutiveOneLineComments) {
  auto tokens = Lex("// line 1\n// line 2\na");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].text, "a");
}

TEST(CommentLexing, OneLineCommentWithSpecialChars) {
  auto tokens = Lex("a // !@#$%^&*(){}[]|<>?\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, BlockCommentStripped) {
  auto tokens = Lex("a /* comment */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, EmptyBlockComment) {
  auto tokens = Lex("a /**/ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, MultiLineBlockComment) {
  auto tokens = Lex("a /* line1\nline2\nline3 */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, BlockCommentOnly) {
  auto tokens = Lex("/* only a comment */");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(CommentLexing, StarsInsideBlockComment) {
  auto tokens = Lex("a /* ** stars ** */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, SlashesInsideBlockComment) {
  auto tokens = Lex("a /* // not a line comment */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, BlockCommentsDoNotNest) {
  auto tokens = Lex("a /* outer /* inner */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, UnterminatedBlockCommentError) {
  auto [tokens, errors] = LexWithDiag("a /* unterminated");
  EXPECT_TRUE(errors);
}

TEST(CommentLexing, LineCommentTokenInsideBlockComment) {
  auto tokens = Lex("a /* // still block */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, BlockCommentTokensInsideLineComment) {
  auto tokens = Lex("a // /* not a block */ still line\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, BlockCommentSeparatesKeywords) {
  auto tokens = Lex("module /* sep */ m;");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "m");
}

TEST(CommentLexing, LineCommentSeparatesKeywords) {
  auto tokens = Lex("module // comment\nm;");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

TEST(CommentLexing, LineCommentAdvancesLineNumber) {
  auto [tokens, errors] = LexWithDiag("a\n// comment\nb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.line, 3u);
}

TEST(CommentLexing, MultiLineBlockCommentAdvancesLineNumber) {
  auto [tokens, errors] = LexWithDiag("a\n/* \n \n */\nb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.line, 5u);
}

}  // namespace
