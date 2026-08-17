#include <set>
#include <string>

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
  EXPECT_EQ(mod->variables[0].name, "genblk1_0_x");
  EXPECT_EQ(mod->variables[1].name, "genblk1_1_x");
  EXPECT_EQ(mod->variables[2].name, "genblk1_2_x");
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
  EXPECT_EQ(mod->variables[0].name, "genblk1_0_w");
  EXPECT_EQ(mod->variables[1].name, "genblk1_1_w");
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
  // The budget is lowered because this case is the only one in the file that
  // reaches it, and its cost is the budget. At the default of 262144 it would
  // elaborate a quarter of a million generate blocks to arrive at a report
  // that says the same thing at 256.
  f.configure = [](Elaborator& elab) { elab.SetMaxGenerateIterations(256); };
  ElabOk(
      "module top();\n"
      "  generate\n"
      "    for (i = 0; i >= 0; i = i + 1) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  // §27.4 states the rule at stake, so the report names it alongside the three
  // other §27.4 rules this file covers. The assertion reads the budget out of
  // the message on purpose: reaching the budget does not establish that a
  // scheme fails to terminate, since one that would have stopped just past it
  // arrives at the same place, and a message asserting non-termination
  // outright would be a claim about this source that the elaborator cannot
  // make. Naming the number is what keeps the report true of both sources that
  // reach it, and naming the budget in force rather than a constant is what
  // lets this case set its own.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "loop generate scheme did not terminate within 256 iterations", 3,
      "27.4"));
}

// A design of this size was refused while the budget was a fixed 65536, and
// §27.4 gives no rule it breaches: the four are a generate block instance
// array name conflicting with another declaration, a scheme that does not
// terminate, a repeated genvar value, and a genvar bit set to x or z. This
// scheme terminates after 65600 iterations, so it elaborates.
//
// The size is just past the old budget on purpose. What the case has to show
// is that a design the elaborator used to refuse now builds, and running it to
// 262143 would cost four times as much and show nothing further.
TEST(GenerateElaboration, LoopGenerateAboveTheOldBoundElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter N = 65600) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->variables.size(), 65600u);
}

// The budget decides in both directions, which is what makes it a budget and
// not a rule: one source, two budgets, two outcomes. Holding the source fixed
// and varying only the budget is what attributes the difference to the budget.
//
// The 300-iteration scheme below terminates, so the rejection under a budget
// of 256 is exactly the defect this case guards against -- a scheme that stops
// on its own, refused for a count §27.4 does not state.
TEST(GenerateElaboration, LoopGenerateBoundDecidesWhetherASchemeIsReported) {
  const std::string kSrc =
      "module t #(parameter N = 300) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n";

  ElabFixture tight;
  tight.configure = [](Elaborator& elab) {
    elab.SetMaxGenerateIterations(256);
  };
  ElaborateSrc(kSrc, tight);
  EXPECT_TRUE(ReportedError(
      tight.diag.Diagnostics(),
      "loop generate scheme did not terminate within 256 iterations", 3,
      "27.4"));

  ElabFixture roomy;
  roomy.configure = [](Elaborator& elab) {
    elab.SetMaxGenerateIterations(1024);
  };
  auto* design = ElaborateSrc(kSrc, roomy);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(roomy.has_errors);
  EXPECT_EQ(design->top_modules[0]->variables.size(), 300u);
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

// Every name the module's variable declarations carry. A set rather than the
// order elaboration produced, because what §27.4 fixes about two sibling
// generate block instance arrays is that their declarations are distinct
// objects: two declarations that collapse onto one name leave one entry here
// whichever order the blocks were visited in.
static std::set<std::string> VariableNames(const RtlirModule* mod) {
  std::set<std::string> names;
  for (const auto& var : mod->variables) names.insert(std::string(var.name));
  return names;
}

// §27.4: a named generate block "is a declaration of an array of generate block
// instances", and "the index values in this array are the values assumed by the
// genvar during elaboration". What identifies an instance is therefore the
// block and the index, not the genvar. Two loop generate constructs written
// side by side over one genvar declare two arrays, and §27.4 rules that a
// generate block "comprises a separate scope", so `blk_a`'s `v` and `blk_b`'s
// `v` are two declarations and the flattened design has to spell them apart.
//
// Naming the flattened declaration after the genvar gave both arrays the prefix
// `i_4_`, so the four declarations collapsed onto two names and one instance's
// `v` answered a reference from the other.
//
// The loop runs over 4 and 5 rather than 0 and 1 so that no index equals the
// storage offset of the variable it names: at 0 and 1 an implementation that
// wrote the offset where §27.4 requires the genvar value would produce the same
// four names.
TEST(GenerateElaboration,
     SiblingNamedBlocksOverOneGenvarNameTheirDeclarationsApart) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 4; i < 6; i = i + 1) begin : blk_a\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "    for (i = 4; i < 6; i = i + 1) begin : blk_b\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 4u);
  EXPECT_EQ(VariableNames(mod),
            (std::set<std::string>{"blk_a_4_v", "blk_a_5_v", "blk_b_4_v",
                                   "blk_b_5_v"}));
}

// §27.4: the same rule reaches the continuous assignments inside the two
// blocks. The body AST is shared across instances and writes the simple name
// the block declared, so an assignment reaches its own instance's declaration
// only through RtlirContAssign::gen_block_prefix (src/elaborator/rtlir.h:226).
// Two sibling arrays over one genvar are separate scopes, so the two
// assignments cannot carry one prefix. Spelling the prefix from the genvar gave
// both of them `i_4_`, and a prefix that does not say which block an assignment
// came from resolves a simple name written in both blocks to one declaration.
//
// The assertion is that the prefixes differ rather than that they read some
// spelling, because §27.4 fixes that the scopes are separate and fixes nothing
// about how a flattened design spells a prefix. ASSERT_FALSE on emptiness
// states the premise the inequality rests on, that both assignments were
// stamped at all: two unstamped assignments agree on the empty string and would
// otherwise be reported as differing from nothing.
TEST(GenerateElaboration,
     SiblingNamedBlocksOverOneGenvarStampDistinctContAssignPrefixes) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 4; i < 5; i = i + 1) begin : blk_a\n"
      "      logic [7:0] a;\n"
      "      assign a = 8'd11;\n"
      "    end\n"
      "    for (i = 4; i < 5; i = i + 1) begin : blk_b\n"
      "      logic [7:0] b;\n"
      "      assign b = 8'd22;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->assigns.size(), 2u);
  std::string first(mod->assigns[0].gen_block_prefix);
  std::string second(mod->assigns[1].gen_block_prefix);
  ASSERT_FALSE(first.empty());
  ASSERT_FALSE(second.empty());
  EXPECT_NE(first, second);
}

// §27.6: "All unnamed generate blocks will be given the name genblk<n> where
// <n> is the number assigned to its enclosing generate construct", numbering
// the constructs of a scope from 1 in textual order. That naming is applied by
// Elaborator::AssignGenerateBlockNames before elaboration, so the two unnamed
// constructs here are `genblk1` and `genblk2`, and the §27.4 rule that
// separates two named sibling arrays separates these two as well.
//
// This is the case that says the separation does not depend on the source
// having written a label: with the prefix spelled from the genvar both unnamed
// blocks were `i_4_` and `i_5_` and their `v` declarations collapsed onto two
// names. The indices are 4 and 5 for the reason the named case gives.
TEST(GenerateElaboration,
     SiblingUnnamedBlocksOverOneGenvarNameTheirDeclarationsApart) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 4; i < 6; i = i + 1) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "    for (i = 4; i < 6; i = i + 1) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 4u);
  EXPECT_EQ(VariableNames(mod),
            (std::set<std::string>{"genblk1_4_v", "genblk1_5_v", "genblk2_4_v",
                                   "genblk2_5_v"}));
}

}  // namespace
