#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §A.9.2:
//   comment           ::= one_line_comment | block_comment
//   one_line_comment  ::= // comment_text \n
//   block_comment     ::= /* comment_text */
//   comment_text      ::= { Any_ASCII_character }
//
// Comments are not emitted as tokens — the lexer skips them as part of
// inter-token whitespace, so production observance is checked by confirming
// that tokens surrounding a comment remain adjacent in the stream and that
// the comment body is consumed up to (but does not appear in) any token.

// --- one_line_comment ---

TEST(CommentLexing, LineCommentSkippedBetweenTokens) {
  auto tokens = Lex("a // line comment\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEof);
}

TEST(CommentLexing, LineCommentTerminatedByNewline) {
  auto tokens = Lex("a //ignored\nb");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  // §A.9.2: newline terminates one_line_comment, so the next token is `b`.
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, LineCommentBodyDoesNotAppearAsToken) {
  auto tokens = Lex("// not_a_token\nx");
  ASSERT_GE(tokens.size(), 2u);
  // §A.9.2: comment_text is consumed inside the comment, not lexed as
  // identifiers or operators.
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "x");
}

TEST(CommentLexing, LineCommentAtEndOfFile) {
  // §A.9.2 / §A.9.4: one_line_comment terminator is \n; per §A.9.4 eof is in
  // the white_space category, so a line comment at EOF is also accepted.
  auto [tokens, errors] = LexWithDiag("x // no newline before eof");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].text, "x");
  EXPECT_EQ(tokens[tokens.size() - 1].kind, TokenKind::kEof);
}

TEST(CommentLexing, LineCommentCanContainAnyAsciiPunctuation) {
  // §A.9.2: comment_text ::= { Any_ASCII_character } — punctuation, operators,
  // and even nested '//' inside the body are all part of the comment.
  auto tokens = Lex("a // !@#$%^&*()_+-=[]{};:'\"<>?,./|\\`~ // still inside\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, LineCommentDoesNotConsumeNewline) {
  // §A.9.2: one_line_comment ::= // comment_text \n — the \n that terminates
  // the comment also acts as white_space (§A.9.4) and the lexer continues on
  // the next line. The line of the following token must therefore advance.
  auto [tokens, errors] = LexWithDiag("// first line\na");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[0].loc.line, 2u);
}

TEST(CommentLexing, EmptyLineComment) {
  // §A.9.2: comment_text ::= { Any_ASCII_character } — { ... } allows zero
  // characters, so `//\n` is a well-formed empty one_line_comment.
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

// --- block_comment ---

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
  // §A.9.2: */ terminates block_comment, so identifiers may immediately
  // follow without intervening whitespace.
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, BlockCommentSpansMultipleLines) {
  // §A.9.2: comment_text ::= { Any_ASCII_character } — newline is an ASCII
  // character and is included in the comment body of a block_comment.
  auto [tokens, errors] = LexWithDiag("a /* line1\nline2\nline3 */ b");
  EXPECT_FALSE(errors);
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
  // The terminator advanced past three newlines, so `b` is on line 3.
  EXPECT_EQ(tokens[1].loc.line, 3u);
}

TEST(CommentLexing, EmptyBlockComment) {
  // §A.9.2: comment_text ::= { ... } admits zero characters; /**/ is valid.
  auto tokens = Lex("a /**/ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, BlockCommentCanContainSlashSlash) {
  // §A.9.2: comment_text inside a block_comment ::= { Any_ASCII_character },
  // so '//' inside /* ... */ is just part of the body, not a nested line
  // comment.
  auto tokens = Lex("a /* not // a line comment */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, BlockCommentDoesNotNest) {
  // §A.9.2: block_comment ::= /* comment_text */ — comment_text is plain
  // ASCII with no recursive production, so the FIRST */ closes the comment.
  // The trailing `*/` is then lexed as ordinary tokens (`*` then `/`).
  auto tokens = Lex("a /* outer /* inner */ x");
  // Tokens: a, x, *, /, EOF (or similar) — the inner `*/` terminated the
  // comment, leaving `x */` after.
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "x");
}

TEST(CommentLexing, BlockCommentCanContainAnyAsciiPunctuation) {
  // §A.9.2: comment_text ::= { Any_ASCII_character } — any ASCII char other
  // than the closing `*/` may appear in the body.
  auto tokens = Lex("a /* !@#$%^&()_+-=[]{};:'\"<>?,.|\\`~ */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, UnterminatedBlockCommentIsAnError) {
  // §A.9.2: block_comment requires `*/`. If the input ends without one, the
  // lexer must report a diagnostic.
  auto [tokens, errors] = LexWithDiag("a /* no closing");
  EXPECT_TRUE(errors);
}

TEST(CommentLexing, BlockCommentJoinsAdjacentTokens) {
  // §A.9.2 with §5.2: a block_comment acts as inter-token whitespace, but a
  // ZERO-width comment between identifier-characters still separates them
  // because the lexer terminates the first identifier at the '/' of `/*`.
  auto tokens = Lex("ab/**/cd");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "ab");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "cd");
}

// --- comment ::= one_line_comment | block_comment ---

TEST(CommentLexing, BothCommentFormsRecognized) {
  // §A.9.2: comment ::= one_line_comment | block_comment — both forms are
  // accepted within the same source.
  auto tokens = Lex(
      "a // line\n"
      "/* block */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(CommentLexing, CommentPreservesSurroundingTokenKinds) {
  // Removing comments must not change the resulting token stream's kinds.
  auto plain = Lex("module m; logic x; endmodule");
  auto with_comments =
      Lex("module /* a */ m; // line\nlogic /**/ x; endmodule // tail");
  // Both must produce the same sequence of token kinds (ignoring EOF
  // alignment — both end with EOF).
  ASSERT_EQ(plain.size(), with_comments.size());
  for (size_t i = 0; i < plain.size(); ++i) {
    EXPECT_EQ(plain[i].kind, with_comments[i].kind) << "index " << i;
  }
}

}  // namespace
