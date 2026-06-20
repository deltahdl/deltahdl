#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(GenerateElaboration, GenerateForCreatesVars) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter N = 3) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      logic [31:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 3u);
  EXPECT_EQ(mod->variables[0].name, "i_0_x");
  EXPECT_EQ(mod->variables[1].name, "i_1_x");
  EXPECT_EQ(mod->variables[2].name, "i_2_x");
}

TEST(GenerateElaboration, GenerateForZeroIterations) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter N = 0) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      logic [31:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 0u);
}

TEST(GenerateElaboration, GenerateForWithAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter N = 2) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      logic [31:0] w;\n"
      "      assign w = 100;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_EQ(mod->assigns.size(), 2u);
  EXPECT_EQ(mod->variables[0].name, "i_0_w");
  EXPECT_EQ(mod->variables[1].name, "i_1_w");
}

TEST(GenerateElaboration, GenerateForCreatesInstances) {
  ElabFixture f;
  auto* design = Elaborate(
      "module sub(input logic a); endmodule\n"
      "module top #(parameter N = 2) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin : blk\n"
      "      sub u(.a(1'b0));\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->children.size(), 2u);
}

TEST(GenerateElaboration, GenerateForStepByTwo) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter N = 6) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 2) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 3u);
}

TEST(GenerateElaboration, GenerateForSingleIteration) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter N = 1) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      logic [7:0] s;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "i_0_s");
}

TEST(GenerateElaboration, NestedGenerateForIf) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter N = 2) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      if (1) begin\n"
      "        logic [7:0] inner;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->variables.size(), 2u);
}

TEST(GenerateElaboration, GenerateForNonTerminatingLoopErrors) {
  EXPECT_FALSE(
      ElabOk("module top();\n"
             "  generate\n"
             "    for (i = 0; i >= 0; i = i + 1) begin\n"
             "      logic [7:0] x;\n"
             "    end\n"
             "  endgenerate\n"
             "endmodule\n"));
}

TEST(GenerateElaboration, GenerateForRepeatedGenvarValueErrors) {
  EXPECT_FALSE(
      ElabOk("module top();\n"
             "  generate\n"
             "    for (i = 5; i < 10; i = 5) begin\n"
             "      logic [7:0] x;\n"
             "    end\n"
             "  endgenerate\n"
             "endmodule\n"));
}

TEST(GenerateElaboration, GenerateForInitStepDifferentVariablesErrors) {
  EXPECT_FALSE(
      ElabOk("module top();\n"
             "  genvar i, j;\n"
             "  generate\n"
             "    for (i = 0; i < 3; j = j + 1) begin\n"
             "      logic [7:0] x;\n"
             "    end\n"
             "  endgenerate\n"
             "endmodule\n"));
}

TEST(GenerateElaboration, GenerateForInitReferencesOwnGenvarErrors) {
  EXPECT_FALSE(
      ElabOk("module top();\n"
             "  generate\n"
             "    for (i = i + 1; i < 3; i = i + 1) begin\n"
             "      logic [7:0] x;\n"
             "    end\n"
             "  endgenerate\n"
             "endmodule\n"));
}

// §27.4: a named loop generate block declares a generate block instance array,
// and its name conflicting with another declaration in the same scope is an
// error. Here the block name collides with a variable. The loop also runs zero
// times, exercising the rule that the array is declared even when the scheme
// produces no instances.
TEST(GenerateElaboration, GenerateForNamedBlockConflictsWithVariableErrors) {
  EXPECT_FALSE(
      ElabOk("module top();\n"
             "  logic a;\n"
             "  genvar i;\n"
             "  generate\n"
             "    for (i = 1; i < 0; i = i + 1) begin : a\n"
             "      logic [7:0] x;\n"
             "    end\n"
             "  endgenerate\n"
             "endmodule\n"));
}

// §27.4: the conflict rule explicitly covers a clash between two generate block
// instance arrays. Two loop generate blocks sharing one array name in the same
// scope is an error.
TEST(GenerateElaboration, GenerateForDuplicateBlockArrayNameErrors) {
  EXPECT_FALSE(
      ElabOk("module top();\n"
             "  genvar i;\n"
             "  generate\n"
             "    for (i = 1; i < 5; i = i + 1) begin : a\n"
             "      logic [7:0] x;\n"
             "    end\n"
             "    for (i = 10; i < 15; i = i + 1) begin : a\n"
             "      logic [7:0] y;\n"
             "    end\n"
             "  endgenerate\n"
             "endmodule\n"));
}

// §27.4: it shall be an error if any bit of the genvar is set to x or z
// during evaluation of the loop generate scheme. A genvar initialized to a
// 4-state literal carries an x bit, so the elaborator rejects it with a
// dedicated x/z diagnostic rather than a generic constant-expression error.
TEST(GenerateElaboration, GenerateForGenvarXZInitErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  generate\n"
      "    for (i = 2'b1x; i < 3; i = i + 1) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  // Without the dedicated x/z rule the init case is only a warning and the
  // step case silently ends the loop; the rule turns both into errors.
  EXPECT_TRUE(f.has_errors);
}

// §27.4: the x/z prohibition holds throughout the loop, not just at
// initialization. A step expression that drives the genvar to a z bit is an
// error reported by the same dedicated diagnostic.
TEST(GenerateElaboration, GenerateForGenvarXZStepErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  generate\n"
      "    for (i = 0; i < 3; i = 2'b0z) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  // Without the dedicated x/z rule the init case is only a warning and the
  // step case silently ends the loop; the rule turns both into errors.
  EXPECT_TRUE(f.has_errors);
}

// §27.4: a loop generate block may consist of a single item that is not
// wrapped in begin-end. It is still a generate block and is instantiated once
// per loop index value, so a begin-less body yields one declaration copy per
// iteration just as a begin-end body would.
TEST(GenerateElaboration, GenerateForSingleItemBodyWithoutBeginEnd) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter N = 3) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1)\n"
      "      logic [7:0] v;\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 3u);
}

}  // namespace
