#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ContinuousAssignPreprocessor, BasicContinuousAssign) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  wire a, b;\n"
                              "  assign a = b;\n"
                              "endmodule\n"));
}

TEST(ContinuousAssignPreprocessor, MacroExpandedRhs) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define VAL 1'b1\n"
                              "module m;\n"
                              "  wire y;\n"
                              "  assign y = `VAL;\n"
                              "endmodule\n"));
}

TEST(ContinuousAssignPreprocessor, ConditionalCompilationAroundAssign) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define USE_ASSIGN\n"
                              "module m;\n"
                              "  wire a, b;\n"
                              "`ifdef USE_ASSIGN\n"
                              "  assign a = b;\n"
                              "`endif\n"
                              "endmodule\n"));
}

TEST(NetAliasPreprocessor, BasicNetAlias) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  wire a, b;\n"
                              "  alias a = b;\n"
                              "endmodule\n"));
}

TEST(NetAliasPreprocessor, NetAliasWithMacro) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define LINK alias a = b\n"
                              "module m;\n"
                              "  wire a, b;\n"
                              "  `LINK;\n"
                              "endmodule\n"));
}

}  // namespace
