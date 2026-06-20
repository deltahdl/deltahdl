#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(ParallelBlockPreprocessor, MacroExpansionInsideForkJoin) {
  PreprocFixture f;
  Preprocess(
      "`define ASSIGN_A a = 1;\n"
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      `ASSIGN_A\n"
      "      b = 2;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParallelBlockPreprocessor, MacroExpandsToForkJoinContent) {
  PreprocFixture f;
  Preprocess(
      "`define FORK_BODY fork a = 1; b = 2; join\n"
      "module m;\n"
      "  initial begin\n"
      "    `FORK_BODY\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
