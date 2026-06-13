#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(CommentLexing, LineCommentSkippedBetweenTokens) {
  auto tokens = Lex("a // line comment\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEof);
}

TEST(CommentLexing, LineCommentAtEndOfFile) {

  auto [tokens, errors] = LexWithDiag("x // no newline before eof");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].text, "x");
  EXPECT_EQ(tokens[tokens.size() - 1].kind, TokenKind::kEof);
}

TEST(CommentLexing, LineCommentCanContainAnyAsciiPunctuation) {

  auto tokens = Lex("a // !@#$%^&*()_+-=[]{};:'\"<>?,./|\\`~ // still inside\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, LineCommentDoesNotConsumeNewline) {

  auto [tokens, errors] = LexWithDiag("// first line\na");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[0].loc.line, 2u);
}

TEST(CommentLexing, EmptyLineComment) {

  auto tokens = Lex("a //\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, ConsecutiveLineComments) {
  auto tokens = Lex("a // one\n// two\n// three\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, BlockCommentSkippedBetweenTokens) {
  auto tokens = Lex("a /* block */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, BlockCommentTerminatedByStarSlash) {
  auto tokens = Lex("a /* body */b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");

  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, BlockCommentSpansMultipleLines) {

  auto [tokens, errors] = LexWithDiag("a /* line1\nline2\nline3 */ b");
  EXPECT_FALSE(errors);
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");

  EXPECT_EQ(tokens[1].loc.line, 3u);
}

TEST(CommentLexing, EmptyBlockComment) {

  auto tokens = Lex("a /**/ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, BlockCommentCanContainSlashSlash) {

  auto tokens = Lex("a /* not // a line comment */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, BlockCommentDoesNotNest) {

  auto tokens = Lex("a /* outer /* inner */ x");

  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "x");
}

TEST(CommentLexing, BlockCommentCanContainAnyAsciiPunctuation) {

  auto tokens = Lex("a /* !@#$%^&()_+-=[]{};:'\"<>?,.|\\`~ */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, UnterminatedBlockCommentIsAnError) {

  auto [tokens, errors] = LexWithDiag("a /* no closing");
  EXPECT_TRUE(errors);
}

TEST(CommentLexing, BlockCommentJoinsAdjacentTokens) {

  auto tokens = Lex("ab/**/cd");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "ab");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "cd");
}

TEST(CommentLexing, BothCommentFormsRecognized) {

  auto tokens = Lex(
      "a // line\n"
      "/* block */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, CommentPreservesSurroundingTokenKinds) {

  auto plain = Lex("module m; logic x; endmodule");
  auto with_comments =
      Lex("module /* a */ m; // line\nlogic /**/ x; endmodule // tail");

  ASSERT_EQ(plain.size(), with_comments.size());
  for (size_t i = 0; i < plain.size(); ++i) {
    EXPECT_EQ(plain[i].kind, with_comments[i].kind) << "index " << i;
  }
}

// one_line_comment ::= // comment_text \n with comment_text containing block
// delimiters: a "/*" or "*/" inside a line comment is ordinary comment_text, so
// it neither opens a block nor produces tokens; the comment still ends at \n.
TEST(CommentLexing, LineCommentCanContainBlockDelimiters) {
  auto tokens = Lex("a // /* not a block */ still line\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

// block_comment ::= /* comment_text */: only the "*/" pair terminates the
// comment, so a lone '*' that is not followed by '/' is ordinary comment_text.
TEST(CommentLexing, BlockCommentLoneAsteriskDoesNotClose) {
  auto tokens = Lex("a /* x * y * z */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

}
