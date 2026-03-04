#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

TEST(LexerCh504, BasicLineComment) {
  auto tokens = Lex("a // this is a comment\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEof);
}

TEST(LexerCh504, LineCommentAtEndOfFile) {
  auto tokens = Lex("a // comment at end");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(LexerCh504, EmptyLineComment) {
  auto tokens = Lex("a //\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, LineCommentOnlyInput) {
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
  auto tokens = Lex("a // /* not a block comment */ still line comment\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, BlockOpenInsideLineCommentDoesNotStartBlock) {
  auto tokens = Lex("a // has /* here\nb // no block\nc");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].text, "c");
}

TEST(LexerCh504, BasicBlockComment) {
  auto tokens = Lex("a /* comment */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, EmptyBlockComment) {
  auto tokens = Lex("a /**/ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, MultiLineBlockComment) {
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
  auto tokens = Lex("a /* c1 *//* c2 */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, StarsInsideBlockComment) {
  auto tokens = Lex("a /* ** * *** */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, SlashesInsideBlockComment) {
  auto tokens = Lex("a /* / // /// */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, BlockCommentsDoNotNest) {
  auto tokens = Lex("a /* outer /* inner */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, NestedBlockCommentLeavesDangling) {
  auto tokens = Lex("a /* x /* y */ z */");
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "z");
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[3].kind, TokenKind::kSlash);
}

TEST(LexerCh504, UnterminatedBlockCommentError) {
  auto [tokens, errors] = LexWithDiag("/* no end");
  EXPECT_TRUE(errors);
}

TEST(LexerCh504, UnterminatedBlockCommentAtEof) {
  auto [tokens, errors] = LexWithDiag("a /* unterminated");
  EXPECT_TRUE(errors);
}

TEST(LexerCh504, UnterminatedBlockCommentWithStars) {
  auto [tokens, errors] = LexWithDiag("/* almost ***");
  EXPECT_TRUE(errors);
}

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

TEST(LexerCh504, SingleSlashIsDivide) {
  auto tokens = Lex("a / b");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSlash);
  EXPECT_EQ(tokens[2].text, "b");
}

TEST(LexerCh504, LineCommentAdvancesLineNumber) {
  auto [tokens, errors] = LexWithDiag("a\n// comment\nb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.line, 3u);
}

TEST(LexerCh504, MultiLineBlockCommentAdvancesLineNumber) {
  auto [tokens, errors] = LexWithDiag("a /* line1\nline2\nline3 */ b");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.line, 3u);
}

TEST(LexerCh504, BlockCommentSameLinePreservesColumn) {
  auto [tokens, errors] = LexWithDiag("a /* x */ b");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[0].loc.column, 1u);
  EXPECT_EQ(tokens[1].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.column, 11u);
}

TEST(LexerCh504, LineCommentWithSpecialChars) {
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

TEST(LexerCh504, CommentBetweenModuleKeywordAndName) {
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

TEST(LexerCh504, CommentOnlyInputMultipleTypes) {
  auto tokens = Lex("// line\n/* block */\n// another line");
  ASSERT_EQ(tokens.size(), 1);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexerCh504, EmptyInput) {
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexerCh504, BlockCommentContainingNewlines) {
  auto tokens = Lex("a /*\n\n\n*/ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, SlashStarSlashIsValidBlockComment) {
  auto [tokens, errors] = LexWithDiag("/*/");
  EXPECT_TRUE(errors);
}

TEST(LexerCh504, SlashStarStarSlashIsMinimalBlockComment) {
  auto tokens = Lex("a /**/ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, NoErrorsForValidComments) {
  auto [tokens, errors] = LexWithDiag(
      "module m; // line comment\n"
      "  /* block comment */\n"
      "  logic x; /* another */ // and another\n"
      "endmodule\n");
  EXPECT_FALSE(errors);
}
