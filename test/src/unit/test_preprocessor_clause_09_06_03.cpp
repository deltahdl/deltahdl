#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(DisableForkPreprocessor, DisableForkSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  initial begin\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("disable"), std::string::npos);
  EXPECT_NE(result.find("fork"), std::string::npos);
}

TEST(DisableForkPreprocessor, ConditionalCompilationAroundDisableFork) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define USE_DISABLE_FORK\n"
      "module m;\n"
      "  initial begin\n"
      "`ifdef USE_DISABLE_FORK\n"
      "    disable fork;\n"
      "`endif\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("disable"), std::string::npos);
}

TEST(DisableForkPreprocessor, ConditionalCompilationExcludesDisableFork) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  initial begin\n"
      "`ifdef USE_DISABLE_FORK\n"
      "    disable fork;\n"
      "`endif\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("disable"), std::string::npos);
}

}  // namespace
