#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, ResetallDirective) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`resetall\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, ResetallBeforeMultipleModules) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`resetall\n"
                              "module m1;\n"
                              "endmodule\n"
                              "module m2;\n"
                              "endmodule\n"));
}

}  // namespace
