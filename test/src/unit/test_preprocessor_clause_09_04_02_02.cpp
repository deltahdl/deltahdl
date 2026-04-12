#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(ImplicitEventPreprocessor, AtStarSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  always @* y = a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@"), std::string::npos);
  EXPECT_NE(result.find("*"), std::string::npos);
}

TEST(ImplicitEventPreprocessor, AtStarParenSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  always @(*) y = a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(*)"), std::string::npos);
}

TEST(ImplicitEventPreprocessor, MacroInAtStarBody) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ASSIGN y = a & b;\n"
      "module m;\n"
      "  always @* `ASSIGN\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("a & b"), std::string::npos);
}

TEST(ImplicitEventPreprocessor, MacroExpandingToAtStar) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define SENS @*\n"
      "module m;\n"
      "  always `SENS y = a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ImplicitEventPreprocessor, MacroExpandingToAtStarParen) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define SENS @(*)\n"
      "module m;\n"
      "  always `SENS y = a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ImplicitEventPreprocessor, IfdefAroundAtStarBody) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define USE_AND\n"
      "module m;\n"
      "  always @* begin\n"
      "`ifdef USE_AND\n"
      "    y = a & b;\n"
      "`else\n"
      "    y = a | b;\n"
      "`endif\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("a & b"), std::string::npos);
  EXPECT_EQ(result.find("a | b"), std::string::npos);
}

}  // namespace
