// Canonical tests for IEEE 1800-2023 Annex A.9.2 (Comments) at the
// preprocessor stage. The grammar in A.9.2 is also recognized by the
// preprocessor's comment stripper (src/preprocessor/preprocessor.cpp,
// StripComments / StripNormalChar / StripBlockCommentContent and the
// block-comment line handlers), which keeps comment bodies out of directive and
// macro processing and hands each comment on to the lexer with its text. These
// tests observe that production code applying each A.9.2 production by
// inspecting the preprocessed text: a comment's body carries a usage of the
// macro M, which is expanded where the text is code and left as written where
// it is a comment.
//
// The four A.9.2 productions exercised here:
//   comment       ::= one_line_comment | block_comment
//   one_line_comment ::= // comment_text \n
//   block_comment ::= /* comment_text */
//   comment_text  ::= { Any_ASCII_character }
//
// Lexer-stage observation of the same grammar lives in the sibling canonical
// file test_lexer_annex_a_09_02.cpp.

#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

// Defines the macro M whose usages the cases below place in comments and in
// code, so that whether a usage was expanded tells which of the two it was.
constexpr char kDefineM[] = "`define M EXPANDED\n";

// Helpers: does the preprocessed output contain the given substring?
bool Contains(const std::string& haystack, const std::string& needle) {
  return haystack.find(needle) != std::string::npos;
}

// one_line_comment ::= // comment_text \n
// The body following "//" on the same line is comment text: it passes through
// as written, its macro usage unexpanded.
TEST(CommentPreprocessing, LineCommentBodyPassesThroughUnexpanded) {
  PreprocFixture f;
  auto out = Preprocess(std::string(kDefineM) + "alpha // beta `M gamma\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha // beta `M gamma\n"));
  EXPECT_FALSE(Contains(out, "EXPANDED"));
}

// block_comment ::= /* comment_text */
// The body between the delimiters passes through as written, and code
// following "*/" on the same line is expanded as code.
TEST(CommentPreprocessing, BlockCommentBodyPassesThroughUnexpanded) {
  PreprocFixture f;
  auto out =
      Preprocess(std::string(kDefineM) + "alpha /* beta `M */ gamma `M\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha /* beta `M */ gamma EXPANDED\n"));
}

// block_comment with comment_text containing a nested "/*": comment_text is
// any ASCII, so the inner "/*" is ordinary text and the first "*/" closes the
// comment. Text after that "*/" is real code.
TEST(CommentPreprocessing, BlockCommentDoesNotNest) {
  PreprocFixture f;
  auto out = Preprocess(
      std::string(kDefineM) + "alpha /* outer /* inner `M */ `M tail\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha /* outer /* inner `M */ EXPANDED tail\n"));
}

// comment_text ::= { Any_ASCII_character } with zero repetitions: an empty
// block comment "/**/" is a valid comment that separates adjacent tokens.
TEST(CommentPreprocessing, EmptyBlockCommentSeparatesTokens) {
  PreprocFixture f;
  auto out = Preprocess("alpha/**/beta\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha"));
  EXPECT_TRUE(Contains(out, "beta"));
  EXPECT_TRUE(Contains(out, "/**/"));
}

// block_comment spanning multiple lines: an unterminated "/*" on one line opens
// a block whose text runs on to the next line, and a later "*/" closes it so
// following code returns.
TEST(CommentPreprocessing, BlockCommentSpansMultipleLines) {
  PreprocFixture f;
  auto out = Preprocess(std::string(kDefineM) +
                            "alpha /* opencomment `M\n"
                            "closecomment `M */ beta `M\n",
                        f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha /* opencomment `M\n"));
  EXPECT_TRUE(Contains(out, "closecomment `M */ beta EXPANDED\n"));
}

// comment_text ::= { Any_ASCII_character }: arbitrary ASCII punctuation that
// would otherwise tokenize is consumed as comment body. The newline also
// terminates the one_line_comment, so the following line is code.
TEST(CommentPreprocessing, LineCommentConsumesArbitraryAscii) {
  PreprocFixture f;
  auto out = Preprocess(std::string(kDefineM) +
                            "alpha // !@#$%^&*()_+={}|punct `M\n"
                            "delta `M\n",
                        f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha // !@#$%^&*()_+={}|punct `M\n"));
  EXPECT_TRUE(Contains(out, "delta EXPANDED\n"));
}

// comment ::= one_line_comment | block_comment: both alternatives are
// recognized within a single source, and both bodies pass through unexpanded.
TEST(CommentPreprocessing, BothCommentFormsRecognized) {
  PreprocFixture f;
  auto out = Preprocess(std::string(kDefineM) +
                            "alpha // lineword `M\n"
                            "/* blockword `M */ beta\n",
                        f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha // lineword `M\n"));
  EXPECT_TRUE(Contains(out, "/* blockword `M */ beta\n"));
  EXPECT_FALSE(Contains(out, "EXPANDED"));
}

// comment_text ::= { Any_ASCII_character } inside a block comment: arbitrary
// ASCII punctuation between the delimiters is consumed as comment body.
TEST(CommentPreprocessing, BlockCommentConsumesArbitraryAscii) {
  PreprocFixture f;
  auto out = Preprocess(
      std::string(kDefineM) + "alpha /* ;:@#$%&!?punct `M */ beta\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha /* ;:@#$%&!?punct `M */ beta\n"));
  EXPECT_FALSE(Contains(out, "EXPANDED"));
}

// comment_text ::= { Any_ASCII_character } with zero repetitions for the line
// form: an empty line comment "//" is valid and leaves surrounding code intact.
TEST(CommentPreprocessing, EmptyLineComment) {
  PreprocFixture f;
  auto out = Preprocess(
      "alpha //\n"
      "beta\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha"));
  EXPECT_TRUE(Contains(out, "beta"));
}

// one_line_comment takes precedence over a "/*" that follows "//" on the same
// line: the "/*" is comment_text, not a block opener, so the rest of the line
// (including a "*/") is comment and the next line is ordinary code.
TEST(CommentPreprocessing, LineCommentContainsBlockOpen) {
  PreprocFixture f;
  auto out = Preprocess(std::string(kDefineM) +
                            "alpha // /* not a block */ tail `M\n"
                            "beta `M\n",
                        f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha // /* not a block */ tail `M\n"));
  EXPECT_TRUE(Contains(out, "beta EXPANDED\n"));
}

// block_comment with comment_text containing "//": the "//" inside /* */ is
// ordinary comment body, so it does not start a line comment and the "*/" still
// closes the block; code after the close is expanded as code.
TEST(CommentPreprocessing, BlockCommentContainsLineMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      std::string(kDefineM) + "alpha /* inside // marker `M */ beta `M\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha /* inside // marker `M */ beta EXPANDED\n"));
}

// A comment begins where a lexical token may begin, and §5.2 makes a string
// literal one token: a "//" inside A.8.8's triple_quoted_string, whose items
// are any ASCII character but '\', is string content and no one_line_comment.
// The lone '"' inside the string is one of those items, not the string's end,
// so the "//" behind it is still inside.
TEST(CommentPreprocessing, LineMarkerInsideTripleQuotedStringWithLoneQuote) {
  PreprocFixture f;
  auto out = Preprocess("x = \"\"\"a\"b // c\"\"\";\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "\"\"\"a\"b // c\"\"\";"));
}

// The same for "/*": inside a triple_quoted_string it opens no block_comment,
// and the "*/" behind it closes none, so the text between them stands and the
// line after the string is read as code.
TEST(CommentPreprocessing, BlockMarkersInsideTripleQuotedString) {
  PreprocFixture f;
  auto out = Preprocess("x = \"\"\"a\"b /* c */ d\"\"\";\ny = 1;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "/* c */ d\"\"\";"));
  EXPECT_TRUE(Contains(out, "y = 1;"));
}

// A triple_quoted_string spans lines, so a "//" on a later line of one is
// still string content, here behind a '\' that ends the first line as the
// string_escape_seq over the newline; the string's end on the third line
// closes it, and the comment behind that end is a one_line_comment.
TEST(CommentPreprocessing, LineMarkerOnLaterLineOfTripleQuotedString) {
  PreprocFixture f;
  auto out = Preprocess(std::string(kDefineM) +
                            "x = \"\"\"first\\\n// second\n\"\"\"; "
                            "// tail `M\n",
                        f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "// second"));
  EXPECT_TRUE(Contains(out, "\"\"\"; // tail `M\n"));
  EXPECT_FALSE(Contains(out, "EXPANDED"));
}

// A one_line_comment behind a closed triple_quoted_string is a comment as
// behind any token: its body passes through unexpanded.
TEST(CommentPreprocessing, LineCommentAfterTripleQuotedString) {
  PreprocFixture f;
  auto out = Preprocess(
      std::string(kDefineM) + "x = \"\"\"a\"b\"\"\"; // tail `M\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "\"\"\"a\"b\"\"\"; // tail `M\n"));
  EXPECT_FALSE(Contains(out, "EXPANDED"));
}

// A '\' inside a triple_quoted_string opens A.8.8's string_escape_seq, so the
// '"' behind it is the sequence's and the `"""` it begins closes nothing; the
// string ends at the `"""` after it, and the comment behind that is a comment
// whose body passes through unexpanded.
TEST(CommentPreprocessing, EscapedQuoteInsideTripleQuotedStringClosesNothing) {
  PreprocFixture f;
  auto out = Preprocess(
      std::string(kDefineM) + "x = \"\"\"a\\\"\"\"b\"\"\"; // tail `M\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "\"\"\"a\\\"\"\"b\"\"\"; // tail `M\n"));
  EXPECT_FALSE(Contains(out, "EXPANDED"));
}

}  // namespace
