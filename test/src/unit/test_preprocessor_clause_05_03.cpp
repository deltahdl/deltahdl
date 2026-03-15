#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(WhiteSpacePreprocessor, SpaceDelimiterPreserved) {
  PreprocFixture f;
  auto result = Preprocess("module t; logic a; endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(WhiteSpacePreprocessor, TabDelimiterPreserved) {
  PreprocFixture f;
  auto result = Preprocess("module\tt;\tlogic\ta;\tendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(WhiteSpacePreprocessor, NewlineDelimiterPreserved) {
  PreprocFixture f;
  auto result = Preprocess("module\nt\n;\nlogic\na\n;\nendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(WhiteSpacePreprocessor, FormfeedDelimiterPreserved) {
  PreprocFixture f;
  auto result = Preprocess("module\ft\f;\flogic\fa\f;\fendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(WhiteSpacePreprocessor, VerticalTabDelimiterPreserved) {
  PreprocFixture f;
  auto result = Preprocess("module\vt\v;\vlogic\va\v;\vendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(WhiteSpacePreprocessor, CrlfDelimiterPreserved) {
  PreprocFixture f;
  auto result =
      Preprocess("module t;\r\nlogic a;\r\nendmodule\r\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(WhiteSpacePreprocessor, WhitespaceOnlyInput) {
  PreprocFixture f;
  auto result = Preprocess("   \t\n\f\v\r\n   ", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(WhiteSpacePreprocessor, MacroExpansionWithMixedWhitespace) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define VAL 8'd42\n"
      "module\tt\f;\nlogic\v[7:0]\ta;\nassign\fa\t=\n`VAL\f;\vendmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(WhiteSpacePreprocessor, BlanksInStringPreserved) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  initial $display(\"  hello   world  \");\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("  hello   world  "), std::string::npos);
}

TEST(WhiteSpacePreprocessor, TabsInStringPreserved) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  initial $display(\"\thello\tworld\t\");\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\thello\tworld\t"), std::string::npos);
}

}  // namespace
