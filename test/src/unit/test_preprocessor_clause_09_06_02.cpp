#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(DisableStatementPreprocessor, DisableKeywordSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  initial begin : blk\n"
      "    disable blk;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("disable"), std::string::npos);
}

TEST(DisableStatementPreprocessor, MacroExpansionInDisableTarget) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define BLK_NAME my_blk\n"
      "module m;\n"
      "  initial begin : my_blk\n"
      "    disable `BLK_NAME;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("disable"), std::string::npos);
}

TEST(DisableStatementPreprocessor, ConditionalCompilationAroundDisable) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define HAS_RESET\n"
      "module m;\n"
      "  initial begin : blk\n"
      "`ifdef HAS_RESET\n"
      "    disable blk;\n"
      "`endif\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("disable"), std::string::npos);
}

TEST(DisableStatementPreprocessor, ConditionalCompilationExcludesDisable) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  initial begin : blk\n"
      "`ifdef HAS_RESET\n"
      "    disable blk;\n"
      "`endif\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("disable"), std::string::npos);
}

}  // namespace
