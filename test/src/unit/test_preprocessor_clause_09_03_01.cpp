#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(SequentialBlockPreprocessor, MacroExpansionInsideSeqBlock) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ASSIGN_A a = 1;\n"
      "module m;\n"
      "  initial begin\n"
      "    `ASSIGN_A\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SequentialBlockPreprocessor, MacroExpandsToSeqBlockContent) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define BODY begin a = 1; b = 2; end\n"
      "module m;\n"
      "  initial `BODY\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
