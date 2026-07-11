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

// §27.4: the implicit localparam inside a loop generate block has the same name
// as the genvar and shadows it, so two nested loop generate constructs cannot
// use the same genvar -- inside the inner loop the name already refers to the
// outer block's localparam. This is LRM Example 1, module mod_a, which the
// standard flags as an error.
TEST(GenerateElaboration, NestedLoopGenerateSameGenvarErrors) {
  EXPECT_FALSE(
      ElabOk("module mod_a();\n"
             "  genvar i;\n"
             "  for (i = 0; i < 5; i = i + 1) begin : a\n"
             "    for (i = 0; i < 5; i = i + 1) begin : b\n"
             "      logic [7:0] x;\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

// §27.4: nesting loop generate constructs is legal as long as they use distinct
// genvars, so an outer i and an inner j elaborate cleanly to the full cross
// product of instances.
TEST(GenerateElaboration, NestedLoopGenerateDistinctGenvarsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter N = 2) ();\n"
      "  genvar i, j;\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      for (j = 0; j < N; j = j + 1) begin\n"
      "        logic [7:0] x;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 4u);
}

// §27.4: the restriction is only on nesting -- two sibling loop generate
// constructs (one finishing before the other begins) may reuse the same genvar.
// The active-genvar set is cleared when a loop finishes, so the second loop is
// not rejected and both bodies are instantiated.
TEST(GenerateElaboration, SiblingLoopGenerateReuseSameGenvarElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 2; i = i + 1) begin\n"
      "      logic [7:0] a;\n"
      "    end\n"
      "    for (i = 0; i < 2; i = i + 1) begin\n"
      "      logic [7:0] b;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 4u);
}

// §27.4: a named loop generate block declares an array of generate block
// instances whose index values are the values the genvar assumes; these need
// not form a contiguous range, so the array may be sparse. A geometric step
// yields the non-contiguous values 1, 2, 4, 8, producing one instance each.
TEST(GenerateElaboration, GenerateForSparseGenvarRange) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 1; i < 16; i = i * 2) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 4u);
}

// §27.4: the iteration assignment advances the genvar each pass of the loop
// generate scheme. An increment (i++) iteration form assigns to the same
// genvar, so the loop steps 0,1,2,3 and instantiates the block four times.
TEST(GenerateElaboration, GenerateForIncrementIterationForm) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 4; i++) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 4u);
}

// §27.4: the iteration form may also decrement the genvar. A (i--) iteration
// assigns to the same genvar and drives the loop 3,2,1,0, again producing four
// instances -- exercising the decrement branch of the genvar advance.
TEST(GenerateElaboration, GenerateForDecrementIterationForm) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 3; i >= 0; i--) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 4u);
}

// §27.4 (dep §6.20.4): the loop bound is a constant expression, which may be a
// localparam as well as a literal or a module parameter. Built from real
// localparam source syntax and driven through elaboration, the bound resolves
// so the loop instantiates the block once per index value, 0..3.
TEST(GenerateElaboration, GenerateForBoundFromLocalparam) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  localparam N = 4;\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 4u);
}

// §27.4: within a generate block the genvar names an implicit localparam that
// can be used anywhere a normal integer parameter can be used -- including as
// the bound of a nested loop generate scheme. Here the inner loop bound reads
// the outer genvar, so the inner loop runs i times per outer index: i=0 makes
// no instance, i=1 one, i=2 two, for three block instances in all. This
// observes the outer index value being consumed as a constant in the inner
// generate scheme.
TEST(GenerateElaboration, NestedLoopGenerateInnerBoundUsesOuterGenvar) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  genvar i, j;\n"
      "  generate\n"
      "    for (i = 0; i < 3; i = i + 1) begin\n"
      "      for (j = 0; j < i; j = j + 1) begin\n"
      "        logic [7:0] x;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 3u);
}

// §27.4: the same-genvar requirement on the iteration assignment applies to the
// increment/decrement iteration form too, not just the assignment form. A (j++)
// step whose target differs from the init genvar i is rejected, exercising the
// unary-step branch of the same-genvar check.
TEST(GenerateElaboration, GenerateForInitStepMismatchIncrementFormErrors) {
  EXPECT_FALSE(
      ElabOk("module top();\n"
             "  genvar i, j;\n"
             "  generate\n"
             "    for (i = 0; i < 3; j++) begin\n"
             "      logic [7:0] x;\n"
             "    end\n"
             "  endgenerate\n"
             "endmodule\n"));
}

}  // namespace
