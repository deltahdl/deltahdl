#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(CommentPreprocessor, LineCommentPassesThrough) {
  PreprocFixture f;
  Preprocess(
      "module t; // line comment\n"
      "  logic a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, BlockCommentPassesThrough) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  /* block comment */\n"
      "  logic a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, MixedCommentsPassThrough) {
  PreprocFixture f;
  Preprocess(
      "module /* name */ t; // header\n"
      "  logic a; /* decl */\n"
      "  // trailing\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, BlockCommentNotNested) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  logic /* outer /* inner */ a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, LineCommentInsideBlockIgnored) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  /* // not special\n"
      "     still block */\n"
      "  logic a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, BlockTokensInsideLineIgnored) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  // /* not a block */ still line\n"
      "  logic a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, CommentOnlyInput) {
  PreprocFixture f;
  Preprocess(
      "// line comment\n"
      "/* block comment */\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, MultilineBlockCommentSpan) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  /* spanning\n"
      "     multiple\n"
      "     lines */\n"
      "  logic a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, BlockCommentAsSeparator) {
  PreprocFixture f;
  Preprocess("module/**/t;logic/**/a;endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, CommentAfterMacroDefinition) {
  PreprocFixture f;
  Preprocess(
      "`define WIDTH 8 // bus width\n"
      "module t;\n"
      "  logic [`WIDTH-1:0] a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §5.4: a /* inside a one-line comment opens nothing, on a `define line as
// anywhere. Read as an open block comment, it joined every line after it into
// the macro's text, and the module that follows vanished with them.
TEST(CommentPreprocessor, BlockOpenerInALineCommentOnADefineJoinsNoLine) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define M a // see /*\n"
      "module t; endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("module t; endmodule"), std::string::npos);
}

// §5.4 with §5.9: a `/*` inside a string literal opens no block comment, so the
// declaration after the string on the same line reaches the output, and the
// `*/` in the one-line comment that ends the line closes nothing. The same
// holds for the string a macro's text holds and for a triple-quoted string.
TEST(CommentPreprocessor, BlockOpenerInsideAStringOpensNoComment) {
  for (const char* line : {"string s = \"/*\"; int x = 1; // */\n",
                           "string s = `M; int x = 1; // */\n",
                           "string s = \"\"\"/*\"\"\"; int x = 1; // */\n"}) {
    PreprocFixture f;
    auto out =
        Preprocess(std::string("`define M \"/* m\"\n") + line + "int y;\n", f);
    EXPECT_FALSE(f.diag.HasErrors()) << line;
    EXPECT_NE(out.find("int x = 1;"), std::string::npos) << line << out;
    EXPECT_NE(out.find("int y;"), std::string::npos) << line << out;
  }
}

// The string keeps the comment markers as its characters: the text written
// between the quotes reaches the output whole.
TEST(CommentPreprocessor, CommentMarkersInsideAStringStayInIt) {
  PreprocFixture f;
  auto out = Preprocess(
      "string a = \"/*\";\nstring b = \"*/\";\nstring c = \"a // b\";\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("\"/*\""), std::string::npos) << out;
  EXPECT_NE(out.find("\"*/\""), std::string::npos) << out;
  EXPECT_NE(out.find("\"a // b\""), std::string::npos) << out;
}

}  // namespace
