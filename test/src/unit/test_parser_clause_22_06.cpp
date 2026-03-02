// §22.6: `ifdef, `else, `elsif, `endif, `ifndef

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, IfdefDefined) {
  EXPECT_TRUE(
      ParseOk("`define FEATURE_A\n"
              "`ifdef FEATURE_A\n"
              "module t;\n"
              "endmodule\n"
              "`endif\n"));
}

TEST(ParserSection22, IfdefWithElse) {
  EXPECT_TRUE(
      ParseOk("`ifdef UNDEFINED_MACRO\n"
              "module alt;\n"
              "endmodule\n"
              "`else\n"
              "module t;\n"
              "endmodule\n"
              "`endif\n"));
}

}  // namespace
