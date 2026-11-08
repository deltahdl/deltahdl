#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

constexpr char kDefineM[] = "`define M EXPANDED\n";

bool Contains(const std::string& haystack, const std::string& needle) {
  return haystack.find(needle) != std::string::npos;
}

TEST(CommentPreprocessing, LineCommentBodyPassesThroughUnexpanded) {
  PreprocFixture f;
  auto out = Preprocess(std::string(kDefineM) + "alpha // beta `M gamma\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha // beta `M gamma\n"));
  EXPECT_FALSE(Contains(out, "EXPANDED"));
}

TEST(CommentPreprocessing, BlockCommentBodyPassesThroughUnexpanded) {
  PreprocFixture f;
  auto out =
      Preprocess(std::string(kDefineM) + "alpha /* beta `M */ gamma `M\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha /* beta `M */ gamma EXPANDED\n"));
}

TEST(CommentPreprocessing, BlockCommentDoesNotNest) {
  PreprocFixture f;
  auto out = Preprocess(
      std::string(kDefineM) + "alpha /* outer /* inner `M */ `M tail\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha /* outer /* inner `M */ EXPANDED tail\n"));
}

TEST(CommentPreprocessing, EmptyBlockCommentSeparatesTokens) {
  PreprocFixture f;
  auto out = Preprocess("alpha/**/beta\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha"));
  EXPECT_TRUE(Contains(out, "beta"));
  EXPECT_TRUE(Contains(out, "/**/"));
}

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

TEST(CommentPreprocessing, BlockCommentConsumesArbitraryAscii) {
  PreprocFixture f;
  auto out = Preprocess(
      std::string(kDefineM) + "alpha /* ;:@#$%&!?punct `M */ beta\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha /* ;:@#$%&!?punct `M */ beta\n"));
  EXPECT_FALSE(Contains(out, "EXPANDED"));
}

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

TEST(CommentPreprocessing, BlockCommentContainsLineMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      std::string(kDefineM) + "alpha /* inside // marker `M */ beta `M\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "alpha /* inside // marker `M */ beta EXPANDED\n"));
}

TEST(CommentPreprocessing, LineMarkerInsideTripleQuotedStringWithLoneQuote) {
  PreprocFixture f;
  auto out = Preprocess("x = \"\"\"a\"b // c\"\"\";\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "\"\"\"a\"b // c\"\"\";"));
}

TEST(CommentPreprocessing, BlockCommentAfterAStringEndingInAnEscapedBackslash) {
  PreprocFixture f;
  auto out = Preprocess(
      "string s = \"a\\\\\"; /* open\n"
      "`define X 1 */\n"
      "`ifdef X\n"
      "int defined_x;\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Contains(out, "defined_x"));
}

TEST(CommentPreprocessing, BlockCommentAfterAQuoteInsideAnEscapedIdentifier) {
  PreprocFixture f;
  auto out = Preprocess(
      "assign \\a\"b = 1; /* open\n"
      "`define X 1 */\n"
      "`ifdef X\n"
      "int defined_x;\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Contains(out, "defined_x"));
}

TEST(CommentPreprocessing, BlockMarkersInsideTripleQuotedString) {
  PreprocFixture f;
  auto out = Preprocess("x = \"\"\"a\"b /* c */ d\"\"\";\ny = 1;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "/* c */ d\"\"\";"));
  EXPECT_TRUE(Contains(out, "y = 1;"));
}

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

TEST(CommentPreprocessing, LineCommentAfterTripleQuotedString) {
  PreprocFixture f;
  auto out = Preprocess(
      std::string(kDefineM) + "x = \"\"\"a\"b\"\"\"; // tail `M\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "\"\"\"a\"b\"\"\"; // tail `M\n"));
  EXPECT_FALSE(Contains(out, "EXPANDED"));
}

TEST(CommentPreprocessing, EscapedQuoteInsideTripleQuotedStringClosesNothing) {
  PreprocFixture f;
  auto out = Preprocess(
      std::string(kDefineM) + "x = \"\"\"a\\\"\"\"b\"\"\"; // tail `M\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Contains(out, "\"\"\"a\\\"\"\"b\"\"\"; // tail `M\n"));
  EXPECT_FALSE(Contains(out, "EXPANDED"));
}

}  // namespace
