#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, IfdefDefined) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define FEATURE_A\n"
                              "`ifdef FEATURE_A\n"
                              "module t;\n"
                              "endmodule\n"
                              "`endif\n"));
}

TEST(CompilerDirectiveParsing, IfdefWithElse) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`ifdef UNDEFINED_MACRO\n"
                              "module alt;\n"
                              "endmodule\n"
                              "`else\n"
                              "module t;\n"
                              "endmodule\n"
                              "`endif\n"));
}

TEST(CompilerDirectiveParsing, IfndefUndefined) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`ifndef GUARD\n"
                              "`define GUARD\n"
                              "module t;\n"
                              "endmodule\n"
                              "`endif\n"));
}

TEST(CompilerDirectiveParsing, IfdefElsifChain) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define OPT_B\n"
                              "`ifdef OPT_A\n"
                              "module ma;\n"
                              "endmodule\n"
                              "`elsif OPT_B\n"
                              "module mb;\n"
                              "endmodule\n"
                              "`else\n"
                              "module mc;\n"
                              "endmodule\n"
                              "`endif\n"));
}

TEST(CompilerDirectiveParsing, NestedIfdef) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define OUTER\n"
                              "`define INNER\n"
                              "`ifdef OUTER\n"
                              "`ifdef INNER\n"
                              "module t;\n"
                              "endmodule\n"
                              "`endif\n"
                              "`endif\n"));
}

}  // namespace
