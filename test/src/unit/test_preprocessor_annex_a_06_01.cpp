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

TEST(ContinuousAssignPreprocessor, ContinuousAssignWithStrengthAndDelay) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  wire a, b;\n"
                              "  assign (strong0, weak1) #10 a = b;\n"
                              "endmodule\n"));
}

TEST(ContinuousAssignPreprocessor, ListOfNetAssignments) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  wire a, b, c, d;\n"
                              "  assign a = b, c = d;\n"
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

TEST(ContinuousAssignPreprocessor, ListOfVariableAssignments) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  logic x, y;\n"
                              "  assign x = 1'b0, y = 1'b1;\n"
                              "endmodule\n"));
}

TEST(ContinuousAssignPreprocessor, VariableAssignWithDelayControl) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  logic x;\n"
                              "  assign #5 x = 1'b1;\n"
                              "endmodule\n"));
}

TEST(NetAliasPreprocessor, BasicNetAlias) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  wire a, b;\n"
                              "  alias a = b;\n"
                              "endmodule\n"));
}

TEST(NetAliasPreprocessor, NetAliasChain) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  wire a, b, c;\n"
                              "  alias a = b = c;\n"
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
