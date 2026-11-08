#include <gtest/gtest.h>

#include "helpers_preprocess_and_get.h"

TEST(UndefineAllSimulation, UndefineAllThenRedefineSimulatesNewValue) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd10\n"
      "`define WITNESS\n"
      "`undefineall\n"
      "`define VAL 8'd55\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef WITNESS\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = `VAL;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 55u);
}

TEST(UndefineAllSimulation, UndefineAllExcludesConditionalFromSimulation) {
  auto result = PreprocessAndGet(
      "`define USE_ALT\n"
      "`undefineall\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef USE_ALT\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = 8'd22;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 22u);
}

TEST(UndefineAllSimulation, UndefineAllRemovesFunctionLikeMacro) {
  auto result = PreprocessAndGet(
      "`define PICK(a, b) a\n"
      "`define WITNESS\n"
      "`undefineall\n"
      "`define PICK(a, b) b\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef WITNESS\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = `PICK(8'd3, 8'd77);\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 77u);
}

TEST(UndefineAllSimulation, UndefineAllRemovesMacroWithArgumentDefaults) {
  auto result = PreprocessAndGet(
      "`define SCALE(a = 8'd5) a\n"
      "`define WITNESS\n"
      "`undefineall\n"
      "`define SCALE(a = 8'd88) a\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef WITNESS\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = `SCALE();\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 88u);
}

TEST(UndefineAllSimulation, UndefineAllRemovesEscapedIdentifierMacro) {
  auto result = PreprocessAndGet(
      "`define \\VAL@ESC 8'd10\n"
      "`define WITNESS\n"
      "`undefineall\n"
      "`define \\VAL@ESC 8'd23\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef WITNESS\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = `\\VAL@ESC ;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 23u);
}

TEST(UndefineAllSimulation, UndefineAllInFalseBranchLeavesMacroUsable) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd44\n"
      "`ifdef NEVER_DEFINED\n"
      "`undefineall\n"
      "`endif\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 44u);
}

TEST(UndefineAllSimulation, UndefineAllTrailingSameLineTextReachesTheDesign) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd10\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`undefineall initial result = 8'd12;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 12u);
}

TEST(UndefineAllSimulation, UndefineAllInsideProceduralBlockRemovesMacro) {
  auto result = PreprocessAndGet(
      "`define USE_ALT\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "`undefineall\n"
      "  end\n"
      "`ifdef USE_ALT\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = 8'd33;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 33u);
}

TEST(UndefineAllSimulation, LongerNameStartingWithUndefineallExpandsAsMacro) {
  auto result = PreprocessAndGet(
      "`define WIDTH 8\n"
      "`define undefineall_saved 8'd66\n"
      "module t;\n"
      "  logic [`WIDTH-1:0] result;\n"
      "  initial result =\n"
      "`undefineall_saved\n"
      "    ;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 66u);
}
