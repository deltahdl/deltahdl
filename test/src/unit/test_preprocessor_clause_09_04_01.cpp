#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(DelayControlPreprocessor, MacroExpansionInDelayValue) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define DELAY 10\n"
      "module m;\n"
      "  initial #`DELAY a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DelayControlPreprocessor, MacroExpansionInDelayedStatement) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ASSIGN a = 1;\n"
      "module m;\n"
      "  initial #10 `ASSIGN\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DelayControlPreprocessor, MacroExpansionInParenthesizedDelay) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define EXPR (a + b)\n"
      "module m;\n"
      "  initial #`EXPR c = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DelayControlPreprocessor, ZeroDelayWithMacro) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ZERO 0\n"
      "module m;\n"
      "  initial #`ZERO a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DelayControlPreprocessor, DelayControlSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  initial #10 a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("#10"), std::string::npos);
}

}  // namespace
