#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

TEST(Preprocessor, UndefineAllUndefinedAllMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 42\n"
      "`undefineall\n"
      "`ifdef FOO\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

TEST(Preprocessor, UndefineAllMultipleMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define A 1\n"
      "`define B 2\n"
      "`define C 3\n"
      "`undefineall\n"
      "`ifdef A\n"
      "a_visible\n"
      "`endif\n"
      "`ifdef B\n"
      "b_visible\n"
      "`endif\n"
      "`ifdef C\n"
      "c_visible\n"
      "`endif\n",
      f);
  EXPECT_EQ(result.find("a_visible"), std::string::npos);
  EXPECT_EQ(result.find("b_visible"), std::string::npos);
  EXPECT_EQ(result.find("c_visible"), std::string::npos);
}

TEST(Preprocessor, UndefineAllTakesNoArguments) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 1\n"
      "`undefineall\n"
      "int x = 5;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 5;"), std::string::npos);
}

TEST(Preprocessor, UndefineAllCanAppearAnywhere) {
  PreprocFixture f;
  Preprocess(
      "`define FOO 1\n"
      "module m;\n"
      "`undefineall\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, DefineAfterUndefineAll) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 1\n"
      "`undefineall\n"
      "`define BAR 99\n"
      "int x = `BAR;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("99"), std::string::npos);
}

TEST(Preprocessor, UndefineAllIncludesFunctionLikeMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ADD(a,b) a + b\n"
      "`undefineall\n"
      "`ifdef ADD\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_EQ(result.find("visible"), std::string::npos);
}
