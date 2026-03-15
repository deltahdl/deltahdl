#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(CommentPreprocessor, LineCommentPassesThrough) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t; // line comment\n"
      "  logic a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, BlockCommentPassesThrough) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  /* block comment */\n"
      "  logic a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, MixedCommentsPassThrough) {
  PreprocFixture f;
  auto result = Preprocess(
      "module /* name */ t; // header\n"
      "  logic a; /* decl */\n"
      "  // trailing\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, BlockCommentNotNested) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic /* outer /* inner */ a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, LineCommentInsideBlockIgnored) {
  PreprocFixture f;
  auto result = Preprocess(
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
  auto result = Preprocess(
      "module t;\n"
      "  // /* not a block */ still line\n"
      "  logic a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, CommentOnlyInput) {
  PreprocFixture f;
  auto result = Preprocess(
      "// line comment\n"
      "/* block comment */\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, MultilineBlockCommentSpan) {
  PreprocFixture f;
  auto result = Preprocess(
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
  auto result = Preprocess("module/**/t;logic/**/a;endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CommentPreprocessor, CommentAfterMacroDefinition) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define WIDTH 8 // bus width\n"
      "module t;\n"
      "  logic [`WIDTH-1:0] a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
