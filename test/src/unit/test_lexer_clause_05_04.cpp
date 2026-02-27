#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

// Helper that returns tokens AND checks for no errors.
// ---------------------------------------------------------------------------
// §A.9.2 / §5.4: one_line_comment ::= // comment_text \n
// ---------------------------------------------------------------------------

TEST(LexerCh504, BasicLineComment) {
  // §5.4: A one-line comment starts with // and ends with a newline.
  auto tokens = Lex("a // this is a comment\nb");
  ASSERT_EQ(tokens.size(), 3);  // a, b, EOF
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEof);
}

TEST(LexerCh504, LineCommentAtEndOfFile) {
  // §A.9.2: comment_text is zero or more characters; no trailing \n at EOF.
  auto tokens = Lex("a // comment at end");
  ASSERT_EQ(tokens.size(), 2);  // a, EOF
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(LexerCh504, EmptyLineComment) {
  // §A.9.2: comment_text ::= { Any_ASCII_character }, so zero chars is valid.
  auto tokens = Lex("a //\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, LineCommentOnlyInput) {
  // Entire source is a single line comment.
  auto tokens = Lex("// entire file is comment");
  ASSERT_EQ(tokens.size(), 1);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexerCh504, MultipleConsecutiveLineComments) {
  auto tokens = Lex("a\n// line 1\n// line 2\n// line 3\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, BlockCommentTokensInsideLineComment) {
  // §5.4: /* and */ shall not have any special meaning inside a one-line
  // comment.
  auto tokens = Lex("a // /* not a block comment */ still line comment\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, BlockOpenInsideLineCommentDoesNotStartBlock) {
  // §5.4: /* inside // does not start a block comment.
  auto tokens = Lex("a // has /* here\nb // no block\nc");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].text, "c");
}

// ---------------------------------------------------------------------------
// §A.9.2 / §5.4: block_comment ::= /* comment_text */
// ---------------------------------------------------------------------------

TEST(LexerCh504, BasicBlockComment) {
  // §5.4: A block comment starts with /* and ends with */.
  auto tokens = Lex("a /* comment */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, EmptyBlockComment) {
  // §A.9.2: comment_text can be empty.
  auto tokens = Lex("a /**/ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, MultiLineBlockComment) {
  // §5.4: Block comments can span multiple lines.
  auto tokens = Lex("a /* line1\nline2\nline3 */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, BlockCommentOnlyInput) {
  auto tokens = Lex("/* entire file */");
  ASSERT_EQ(tokens.size(), 1);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexerCh504, MultipleBlockComments) {
  auto tokens = Lex("a /* c1 */ /* c2 */ /* c3 */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, AdjacentBlockComments) {
  // Two block comments with no space between them.
  auto tokens = Lex("a /* c1 *//* c2 */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, StarsInsideBlockComment) {
  // §5.4: Only */ ends a block comment; lone * does not.
  auto tokens = Lex("a /* ** * *** */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, SlashesInsideBlockComment) {
  // §5.4: // shall not have any special meaning inside a block comment.
  auto tokens = Lex("a /* / // /// */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

// ---------------------------------------------------------------------------
// §5.4: Block comments shall not be nested.
// ---------------------------------------------------------------------------

TEST(LexerCh504, BlockCommentsDoNotNest) {
  // §5.4: The first */ ends the block comment. The second /* inside is just
  // text. "a /* outer /* inner */ b" => the /* inner is ignored, */ closes
  // comment.
  auto tokens = Lex("a /* outer /* inner */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, NestedBlockCommentLeavesDangling) {
  // "a /* x /* y */ z */" => first */ closes comment,
  // then z is a token, then * and / are operators.
  auto tokens = Lex("a /* x /* y */ z */");
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "z");
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[3].kind, TokenKind::kSlash);
}

// ---------------------------------------------------------------------------
// §5.4: Unterminated block comment (diagnostic)
// ---------------------------------------------------------------------------

TEST(LexerCh504, UnterminatedBlockCommentError) {
  auto [tokens, errors] = LexWithDiag("/* no end");
  EXPECT_TRUE(errors);
}

TEST(LexerCh504, UnterminatedBlockCommentAtEof) {
  auto [tokens, errors] = LexWithDiag("a /* unterminated");
  EXPECT_TRUE(errors);
}

TEST(LexerCh504, UnterminatedBlockCommentWithStars) {
  // Trailing stars but no closing slash.
  auto [tokens, errors] = LexWithDiag("/* almost ***");
  EXPECT_TRUE(errors);
}

// ---------------------------------------------------------------------------
// Mixed comment types
// ---------------------------------------------------------------------------

TEST(LexerCh504, LineCommentFollowedByBlockComment) {
  auto tokens = Lex("a // line\n/* block */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, BlockCommentFollowedByLineComment) {
  auto tokens = Lex("a /* block */ // line\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, MixedCommentsMultipleLines) {
  auto tokens =
      Lex("a // line comment\n"
          "/* block spanning\n"
          "   multiple lines */\n"
          "b // trailing\n");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

// ---------------------------------------------------------------------------
// §5.4: Single '/' is not a comment — it is the divide operator
// ---------------------------------------------------------------------------

TEST(LexerCh504, SingleSlashIsDivide) {
  auto tokens = Lex("a / b");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSlash);
  EXPECT_EQ(tokens[2].text, "b");
}

// ---------------------------------------------------------------------------
// Source location tracking through comments
// ---------------------------------------------------------------------------

TEST(LexerCh504, LineCommentAdvancesLineNumber) {
  // After a line comment, the next token should be on the correct line.
  auto [tokens, errors] = LexWithDiag("a\n// comment\nb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);  // a on line 1
  EXPECT_EQ(tokens[1].loc.line, 3u);  // b on line 3
}

TEST(LexerCh504, MultiLineBlockCommentAdvancesLineNumber) {
  // A block comment spanning 3 lines should advance the line counter.
  auto [tokens, errors] = LexWithDiag("a /* line1\nline2\nline3 */ b");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);  // a on line 1
  EXPECT_EQ(tokens[1].loc.line, 3u);  // b on line 3
}

TEST(LexerCh504, BlockCommentSameLinePreservesColumn) {
  // Block comment on same line: column should advance past comment.
  auto [tokens, errors] = LexWithDiag("a /* x */ b");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[0].loc.column, 1u);  // 'a' at column 1
  EXPECT_EQ(tokens[1].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.column, 11u);  // 'b' at column 11
}

// ---------------------------------------------------------------------------
// §A.9.2: comment_text ::= { Any_ASCII_character }
// ---------------------------------------------------------------------------

TEST(LexerCh504, LineCommentWithSpecialChars) {
  // All printable ASCII plus some control chars should be accepted.
  auto tokens = Lex("a // ~!@#$%^&*()_+-=[]{}|;':\",./<>?\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, BlockCommentWithSpecialChars) {
  auto tokens = Lex("a /* ~!@#$%^&()_+-=[]{}|;':\",./<>? */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, BlockCommentWithTabsAndFormFeed) {
  auto tokens = Lex("a /* \t\t\f */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

// ---------------------------------------------------------------------------
// Comments as whitespace: comments can appear anywhere whitespace is allowed
// ---------------------------------------------------------------------------

TEST(LexerCh504, CommentBetweenModuleKeywordAndName) {
  // Comments serve as token separators just like whitespace.
  auto tokens = Lex("module /* comment */ m;");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "m");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
}

TEST(LexerCh504, LineCommentBetweenTokens) {
  auto tokens = Lex("module // comment\nm;");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].text, "m");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
}

TEST(LexerCh504, CommentBetweenOperatorAndOperand) {
  auto tokens = Lex("a + /* comment */ b");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[2].text, "b");
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

TEST(LexerCh504, CommentOnlyInputMultipleTypes) {
  // No actual tokens — just comments of both types.
  auto tokens = Lex("// line\n/* block */\n// another line");
  ASSERT_EQ(tokens.size(), 1);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexerCh504, EmptyInput) {
  // No comments, no tokens.
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexerCh504, BlockCommentContainingNewlines) {
  // Newlines inside block comments are just part of comment_text.
  auto tokens = Lex("a /*\n\n\n*/ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, SlashStarSlashIsValidBlockComment) {
  // "/*/" has no closing — only one char of text then EOF.
  auto [tokens, errors] = LexWithDiag("/*/");
  EXPECT_TRUE(
      errors);  // unterminated: the comment is "/* /" with no closing */
}

TEST(LexerCh504, SlashStarStarSlashIsMinimalBlockComment) {
  // "/**/" is the minimal non-empty block comment (comment_text is empty).
  auto tokens = Lex("a /**/ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, NoErrorsForValidComments) {
  // Verify no diagnostics are produced for well-formed comments.
  auto [tokens, errors] = LexWithDiag(
      "module m; // line comment\n"
      "  /* block comment */\n"
      "  logic x; /* another */ // and another\n"
      "endmodule\n");
  EXPECT_FALSE(errors);
}
