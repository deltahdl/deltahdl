#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(UndefineAllParsing, UndefineAllInsideDesignElement) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define A 1\n"
                              "module t;\n"
                              "`undefineall\n"
                              "  wire w;\n"
                              "endmodule\n"));
}

TEST(UndefineAllParsing, UndefineAllTrailingTextParsesAsSource) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define A 1\n"
                              "module t;\n"
                              "`undefineall wire w;\n"
                              "endmodule\n"));
}

TEST(UndefineAllParsing, UndefineAllLeavesElseBranchToParse) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define A 1\n"
                              "`undefineall\n"
                              "module t;\n"
                              "`ifdef A\n"
                              "  this is not valid syntax\n"
                              "`else\n"
                              "  wire w;\n"
                              "`endif\n"
                              "endmodule\n"));
}

}  // namespace
