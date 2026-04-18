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

// §27.4 requires that a loop generate terminate. A condition that can never
// become false forces the elaborator's iteration guard to trip.
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

// §27.4 requires each iteration to produce a distinct genvar value. A step
// that leaves the genvar unchanged revisits the same value and must fail.
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

// §27.4 requires the initial assignment and step assignment to operate on
// the same genvar; using different genvars is malformed.
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

// §27.4 treats the initial assignment as a constant expression; it cannot
// read the genvar it is about to define.
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

// §27.4 does not constrain the direction of iteration. A decrementing step
// that eventually fails the condition should elaborate normally.
TEST(GenerateElaboration, GenerateForDecrementingStride) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  generate\n"
      "    for (i = 3; i > 0; i = i - 1) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 3u);
}

}  // namespace
