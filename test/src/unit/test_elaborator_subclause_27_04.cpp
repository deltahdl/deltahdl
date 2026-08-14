#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  generate\n"
      "    for (i = 0; i >= 0; i = i + 1) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  // The report is emitted with Subclause::None() in
  // src/elaborator/elaborator_generate.cpp, because what it states is that the
  // elaborator's own iteration cap was reached, so there is no subclause text
  // to name here.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-for loop did not terminate", 3, ""));
}

TEST(GenerateElaboration, GenerateForRepeatedGenvarValueErrors) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  generate\n"
      "    for (i = 5; i < 10; i = 5) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-for genvar value is repeated during "
                            "evaluation",
                            3, "27.4"));
}

TEST(GenerateElaboration, GenerateForInitStepDifferentVariablesErrors) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  genvar i, j;\n"
      "  generate\n"
      "    for (i = 0; i < 3; j = j + 1) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate-for init and step shall assign to the same genvar", 4, "27.4"));
}

TEST(GenerateElaboration, GenerateForInitReferencesOwnGenvarErrors) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  generate\n"
      "    for (i = i + 1; i < 3; i = i + 1) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-for init shall not reference the loop "
                            "index on the right-hand side",
                            3, "27.4"));
}

// §27.4: a named loop generate block declares a generate block instance array,
// and its name conflicting with another declaration in the same scope is an
// error. Here the block name collides with a variable. The loop also runs zero
// times, exercising the rule that the array is declared even when the scheme
// produces no instances.
TEST(GenerateElaboration, GenerateForNamedBlockConflictsWithVariableErrors) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  logic a;\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 1; i < 0; i = i + 1) begin : a\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block array 'a' conflicts with an "
                            "existing declaration in the same scope",
                            5, "23.9"));
}

// §27.4: the conflict rule explicitly covers a clash between two generate block
// instance arrays. Two loop generate blocks sharing one array name in the same
// scope is an error.
TEST(GenerateElaboration, GenerateForDuplicateBlockArrayNameErrors) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 1; i < 5; i = i + 1) begin : a\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "    for (i = 10; i < 15; i = i + 1) begin : a\n"
      "      logic [7:0] y;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  // The second loop is the one that finds the name taken, so its `for` on
  // line 7 is where the report stands.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block array 'a' conflicts with an "
                            "existing declaration in the same scope",
                            7, "23.9"));
}

// §27.4: a generate block "comprises a separate scope and a new level of
// hierarchy when it is instantiated", so the enclosing scope of a nested array
// is one instance of the outer block rather than the module. The inner array
// 'h' is declared once per instance of 'g', in two different scopes, so the
// second instantiation is not a conflict with the first. Both instances of the
// inner body are elaborated, giving one 'x' per (i, j) pair.
TEST(GenerateElaboration, NestedBlockArrayNameRepeatsPerOuterInstanceOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  genvar i, j;\n"
      "  generate\n"
      "    for (i = 0; i < 2; i = i + 1) begin : g\n"
      "      for (j = 0; j < 2; j = j + 1) begin : h\n"
      "        logic [7:0] x;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->top_modules[0]->variables.size(), 4u);
}

// §27.4: the conflict rule still applies within one generate block instance.
// Two inner arrays written side by side under the same enclosing block share
// that block's scope, so naming both 'h' is an error exactly as it would be at
// module level -- the separate scope belongs to the instance, not to the
// nesting.
TEST(GenerateElaboration, SiblingBlockArrayNamesInsideOneBlockConflictErrors) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  genvar i, j, k;\n"
      "  generate\n"
      "    for (i = 0; i < 2; i = i + 1) begin : g\n"
      "      for (j = 0; j < 2; j = j + 1) begin : h\n"
      "        logic [7:0] x;\n"
      "      end\n"
      "      for (k = 0; k < 2; k = k + 1) begin : h\n"
      "        logic [7:0] y;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  // The second inner loop, on line 8, is the one that finds 'h' taken.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block array 'h' conflicts with an "
                            "existing declaration in the same scope",
                            8, "23.9"));
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
  // step case silently ends the loop; the rule turns both into errors. Both
  // reports stand at the `for` keyword on line 3, so the half of the header
  // the message names is the only thing that separates them.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-for genvar shall not have any bit set to "
                            "x or z during evaluation, and the initialization "
                            "assignment sets one",
                            3, "27.4"));
}

// §27.4: the x/z prohibition holds throughout the loop, not just at
// initialization. An iteration assignment driving the genvar to a z bit is an
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
  // The iteration site names the iteration assignment, which is what
  // separates this case from GenerateForGenvarXZInitErrors: the two reports
  // stand at the same line under the same subclause, so the message is the only
  // thing that can.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-for genvar shall not have any bit set to "
                            "x or z during evaluation, and the iteration "
                            "assignment sets one",
                            3, "27.4"));
}

// The property the two checks exist to be told apart by. Both stand at the
// `for` keyword under §27.4, so while they shared one sentence
// `for (i = 2'b0z; i < 4; i = i + 1)` and `for (i = 0; i < 4; i = 2'b0z)`
// produced identical output and a test written for either was satisfied by the
// other. Each source here puts exactly one x/z literal in the half it is named
// for, and the negative assertion is what says the reports do not overlap.
TEST(GenerateElaboration, GenerateForGenvarXZReportsNameWhichHalfOfTheHeader) {
  constexpr const char* kInitMsg =
      "generate-for genvar shall not have any bit set to x or z during "
      "evaluation, and the initialization assignment sets one";
  constexpr const char* kIterationMsg =
      "generate-for genvar shall not have any bit set to x or z during "
      "evaluation, and the iteration assignment sets one";

  ElabFixture init;
  ElaborateSrc(
      "module top();\n"
      "  generate\n"
      "    for (i = 2'b1x; i < 3; i = i + 1) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      init);
  EXPECT_TRUE(ReportedError(init.diag.Diagnostics(), kInitMsg, 3, "27.4"));
  EXPECT_FALSE(
      ReportedError(init.diag.Diagnostics(), kIterationMsg, 3, "27.4"));

  ElabFixture step;
  ElaborateSrc(
      "module top();\n"
      "  generate\n"
      "    for (i = 0; i < 3; i = 2'b0z) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      step);
  EXPECT_TRUE(ReportedError(step.diag.Diagnostics(), kIterationMsg, 3, "27.4"));
  EXPECT_FALSE(ReportedError(step.diag.Diagnostics(), kInitMsg, 3, "27.4"));
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
  ElabFixture f;
  ElabOk(
      "module mod_a();\n"
      "  genvar i;\n"
      "  for (i = 0; i < 5; i = i + 1) begin : a\n"
      "    for (i = 0; i < 5; i = i + 1) begin : b\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "genvar 'i' is already in use by an enclosing loop "
                            "generate construct",
                            4, "27.4"));
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
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  genvar i, j;\n"
      "  generate\n"
      "    for (i = 0; i < 3; j++) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate-for init and step shall assign to the same genvar", 4, "27.4"));
}

// §27.4: "The genvar is used as an integer during elaboration to evaluate the
// generate loop and create instances of the generate block, but it does not
// exist at simulation time." The sibling tests here observe that through a
// variable count, which a change in how many variables the loop body
// contributes would also move. This one names the claim directly: whatever
// else the module holds, nothing in it is called by the genvar's name.
TEST(GenerateElaboration, GenvarIsNotAmongTheModuleVariables) {
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
  for (const auto& v : mod->variables) {
    EXPECT_NE(v.name, "i");
  }
}

// §27.4: a loop generate block "comprises a separate scope and a new level of
// hierarchy when it is instantiated", so the one instantiation written in the
// body declares its name in a different scope on each iteration. Two iterations
// of `child c1()` are two declarations in two scopes, not two in one.
TEST(GenerateElaboration, LoopIterationsDoNotRedeclareTheSameInstanceName) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child; endmodule\n"
      "module top;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    child c1();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §27.4, the other side of the same scope: separate scopes per iteration do not
// make one iteration's scope permissive. Two instantiations sharing a name
// inside a single loop body land in the same scope on every iteration, so that
// is still a redeclaration.
TEST(GenerateElaboration, TwoInstancesOfOneNameInALoopBodyIsRedeclaration) {
  ElabFixture f;
  Elaborate(
      "module child; endmodule\n"
      "module top;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    child c1();\n"
      "    child c1();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'c1'", 6, "23.9"));
}

// §27.4 scopes the name to its generate block, which leaves an instantiation
// outside any generate block scoped to the module as before. Two instances of
// one name in a module body remain a redeclaration.
TEST(GenerateElaboration, TwoInstancesOfOneNameInAModuleBodyIsRedeclaration) {
  ElabFixture f;
  Elaborate(
      "module child; endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  child c1();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'c1'", 4, "23.9"));
}

// §27.4: the report that rejects a generate-for whose initializer reads its own
// loop index names the subclause stating the rule, so a caller learns which
// rule was enforced without matching the wording of the message.
TEST(GenerateElaboration, GenerateForInitReferencesOwnGenvarNames27_4) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  generate\n"
      "    for (i = i + 1; i < 3; i = i + 1) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  const Diagnostic* d =
      FindDiag(f, "generate-for init shall not reference the loop index");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "27.4");
}

}  // namespace
