#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "lexer/keywords.h"

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
  Preprocess(
      "`define WIDTH 8\n"
      "module t;logic [`WIDTH-1:0] a;endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  PreprocFixture f2;
  Preprocess(
      "`define WIDTH 8\n"
      "module\n  t\n;\n  logic\n  [`WIDTH-1:0]\n  a\n;\nendmodule\n",
      f2);
  EXPECT_FALSE(f2.diag.HasErrors());
}

TEST(LexicalConventionPreprocessor, BlockCommentPreservedThroughPreprocessing) {
  PreprocFixture f;
  Preprocess("module/**/t;endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LexicalConventionPreprocessor, AllTokenCategoriesPassThroughPreprocessor) {
  PreprocFixture f;
  Preprocess(
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
  Preprocess("module\tt\f;\flogic\ta\t;\tendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §5.2 makes a source file a stream of lexical tokens and lists the seven kinds
// there are; kKeywordMarker, the byte 0x01, begins none of them, so a source
// holding one is rejected at the character it stands on.
TEST(LexicalConventionPreprocessor, KeywordMarkerByteInSourceTextIsReported) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  logic \x01 a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unexpected character 0x01 in source text", 2,
                            "5.2"));
}

// What that report protects. The Preprocessor writes kKeywordMarker itself to
// introduce a keyword-version change, and Lexer reads the byte after every
// marker it finds as a KeywordVersion, so a 0x01 the user wrote that survived
// into the output would set the reserved word list to whatever byte followed
// it instead of being diagnosed.
TEST(LexicalConventionPreprocessor,
     KeywordMarkerByteIsBlankedFromPreprocessedText) {
  PreprocFixture f;
  auto out = Preprocess(
      "module t;\n"
      "  logic \x01 a;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out.find(kKeywordMarker), std::string::npos);
}

}  // namespace
