#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(StringLiteralPreprocessor, MacroAfterAContinuedStringExpands) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define W 8\n"
      "module t;\n"
      "  initial $display(\"abc\\\n"
      "\", `W);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("\", 8);"), std::string::npos);
}

TEST(StringLiteralPreprocessor, MacroInsideAContinuedStringStaysText) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define W 8\n"
      "module t;\n"
      "  initial $display(\"abc\\\n"
      "`W\");\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("`W\");"), std::string::npos);
}

TEST(StringLiteralPreprocessor, StringContinuedOverSeveralLines) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define W 8\n"
      "$display(\"a\\\n"
      "b\\\"`W\\\n"
      "c\", `W);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("b\\\"`W\\"), std::string::npos);
  EXPECT_NE(out.find("c\", 8);"), std::string::npos);
}

TEST(StringLiteralPreprocessor, UnescapedNewlineCarriesNoString) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define W 8\n"
      "x = \"abc\n"
      "y = `W;\n",
      f);
  EXPECT_NE(out.find("y = 8;"), std::string::npos);
}

}  // namespace
