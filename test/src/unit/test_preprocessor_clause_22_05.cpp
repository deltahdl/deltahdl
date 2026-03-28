#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

TEST(Preprocessor, ResetAll_PreservesTextMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO bar\n"
      "`resetall\n"
      "int x = `FOO;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("bar"), std::string::npos);
}

TEST(Preprocessor, ResetAll_PreservesMacroWithArguments) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MAX(a,b) ((a)>(b)?(a):(b))\n"
      "`resetall\n"
      "int x = `MAX(3,5);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("((3)>(5)?(3):(5))"), std::string::npos);
}

TEST(Preprocessor, MultipleResetAll_PreservesTextMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define WIDTH 8\n"
      "`resetall\n"
      "`resetall\n"
      "`resetall\n"
      "logic [`WIDTH-1:0] data;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("8"), std::string::npos);
}
