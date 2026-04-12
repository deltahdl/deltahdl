#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(LevelSensitiveEventPreprocessor, MacroExpansionInWaitCondition) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define COND ready\n"
      "module m;\n"
      "  initial wait (`COND) a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LevelSensitiveEventPreprocessor, MacroExpansionInWaitBody) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ASSIGN a = 1;\n"
      "module m;\n"
      "  initial wait (done) `ASSIGN\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LevelSensitiveEventPreprocessor, WaitKeywordSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  initial wait (done) a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("wait"), std::string::npos);
}

}  // namespace
