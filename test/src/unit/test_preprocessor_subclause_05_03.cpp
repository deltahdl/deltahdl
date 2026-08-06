#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(WhiteSpacePreprocessor, VerticalTabDelimiterPreserved) {
  PreprocFixture f;
  Preprocess("module\vt\v;\vlogic\va\v;\vendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(WhiteSpacePreprocessor, CrlfDelimiterPreserved) {
  PreprocFixture f;
  Preprocess("module t;\r\nlogic a;\r\nendmodule\r\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(WhiteSpacePreprocessor, WhitespaceOnlyInput) {
  PreprocFixture f;
  Preprocess("   \t\n\f\v\r\n   ", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(WhiteSpacePreprocessor, MacroExpansionWithMixedWhitespace) {
  PreprocFixture f;
  Preprocess(
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
