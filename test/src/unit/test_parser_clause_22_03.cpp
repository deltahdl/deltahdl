#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, ResetallDirective) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`resetall\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(ParserSection22, ResetallBeforeMultipleModules) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`resetall\n"
                              "module m1;\n"
                              "endmodule\n"
                              "module m2;\n"
                              "endmodule\n"));
}

}
