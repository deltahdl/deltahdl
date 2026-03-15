#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(LexicalConventionPreprocessor, FreeFormatPreservedThroughPreprocessing) {
  PreprocFixture f;
  auto compact = Preprocess("module t;logic a;endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(compact.find("module"), std::string::npos);
  EXPECT_NE(compact.find("endmodule"), std::string::npos);
}

TEST(LexicalConventionPreprocessor, FreeFormatMultilinePreserved) {
  PreprocFixture f;
  auto result = Preprocess(
      "module\n"
      "  t\n"
      ";\n"
      "  logic\n"
      "    a\n"
      ";\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

TEST(LexicalConventionPreprocessor, MacroExpansionPreservesFreeFormat) {
  PreprocFixture f;
  auto compact = Preprocess(
      "`define WIDTH 8\n"
      "module t;logic [`WIDTH-1:0] a;endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  PreprocFixture f2;
  auto spread = Preprocess(
      "`define WIDTH 8\n"
      "module\n  t\n;\n  logic\n  [`WIDTH-1:0]\n  a\n;\nendmodule\n",
      f2);
  EXPECT_FALSE(f2.diag.HasErrors());
}

TEST(LexicalConventionPreprocessor, BlockCommentPreservedThroughPreprocessing) {
  PreprocFixture f;
  auto result = Preprocess("module/**/t;endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LexicalConventionPreprocessor, EscapedIdentifierPreservedThroughPreprocessing) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic \\my+sig ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\\my+sig"), std::string::npos);
}

TEST(LexicalConventionPreprocessor, AllTokenCategoriesPassThroughPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t; // line comment\n"
      "  /* block comment */\n"
      "  logic [7:0] data = 8'hAB;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LexicalConventionPreprocessor, TabsAndFormfeedsAsWhitespace) {
  PreprocFixture f;
  auto result = Preprocess("module\tt\f;\flogic\ta\t;\tendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
