#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate-for init shall not reference the loop index", 3, "27.4"));
}

// §27.4 requires the genvar initialization assignment to be a constant
// expression, and §26.3 makes a wildcard-imported name locally visible only
// "prior to that point within the current scope". The scope holding the import
// is module a, so W names nothing in module b and
// Elaborator::OpenGenerateForLoop in src/elaborator/elaborator_generate.cpp
// warns instead of opening the loop.
//
// What this fails on is W folding in module b anyway, which it does when the
// scope the loop header is evaluated against is assembled after every module
// has been elaborated rather than inside module b.
//
// The imported parameter is the loop's initial value rather than its
// termination bound because a termination condition that does not fold is
// reported nowhere: GenerateForConditionHolds in
// src/elaborator/elaborator_generate.cpp answers false for a condition it
// cannot fold, which stops the loop exactly as a false condition does, so a
// case written on the termination bound would assert on an absence and pass on
// any cause of it. Both expressions are evaluated against the one scope this
// case is about.
//
// The case that the import still reaches the module that wrote it is
// GenerateElaboration.ImportedParameterReachesItsOwnModulesGenerateIf in
// test/src/unit/test_elaborator_subclause_27_05.cpp.
TEST(GenerateElaboration,
     ImportedParameterDoesNotReachAnotherModulesGenerateFor) {
  ElabFixture f;
  ElaborateWithPreprocessor(
      "package p;\n"
      "  parameter int W = 0;\n"
      "endpackage\n"
      "module a;\n"
      "  import p::*;\n"
      "endmodule\n"
      "module b;\n"
      "  for (genvar i = W; i < 3; i = i + 1) begin : g\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f, "", true);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "generate-for init is not constant", 8, "27.4"));
}

// Annex A.8.3 gives `genvar_expression ::= constant_expression`, so the
// termination expression of a loop generate has to fold during elaboration.
// Here it reads the variable n, which does not, and the case fails when nothing
// is reported: GenerateForConditionHolds in
// src/elaborator/elaborator_generate.cpp answers the same false for a condition
// it could not fold as for one that folded to zero, and
// Elaborator::ElaborateGenerateFor breaks the loop on that false, so the run
// produces the design of a zero-trip loop.
//
// The absence of m.g is not what this asserts, because the block is equally
// absent when the source failed to parse and when the loop was legally
// zero-trip.
TEST(GenerateElaboration, GenerateForBoundOnAVariableIsNotConstant) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [3:0] n;\n"
      "  for (genvar i = 0; i < n; i = i + 1) begin : g\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(),
      "generate-for termination expression is not constant", 3, "27.4"));
}

// Annex A.8.3 requires a constant expression of the iteration assignment too,
// through `genvar_iteration ::= genvar_identifier assignment_operator
// genvar_expression`. The bound here folds and the step reads the variable n,
// so this case fails while ComputeGenerateForNextValue in
// src/elaborator/elaborator_generate.cpp returns std::nullopt for an expression
// it cannot fold and Elaborator::ElaborateGenerateFor breaks on it in silence,
// leaving one instance behind. It is separate from the termination expression
// because the two are folded at different sites and a report added to one
// leaves the other quiet.
TEST(GenerateElaboration, GenerateForStepOnAVariableIsNotConstant) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [3:0] n;\n"
      "  for (genvar i = 0; i < 4; i = i + n) begin : g\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "generate-for iteration expression is not constant",
      3, "27.4"));
}

// The form the same defect takes when the bound was meant to name a parameter a
// package exports: W is declared nowhere in module m, so ConstEvalInt cannot
// fold `i < W` and GenerateForConditionHolds in
// src/elaborator/elaborator_generate.cpp answers false. The case fails when the
// run says nothing, which is what makes a misspelled or unimported name
// indistinguishable from a bound of zero.
TEST(GenerateElaboration,
     GenerateForBoundOnAnUndeclaredIdentifierIsNotConstant) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  for (genvar i = 0; i < W; i = i + 1) begin : g\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(),
      "generate-for termination expression is not constant", 2, "27.4"));
}

// A loop generate whose termination expression folds to false is legal and
// creates no instances, which GenerateElaboration.GenerateForZeroIterations
// above already reads off the variable count. This case is the other half of
// that claim: the run has to stay quiet about it. It fails when the report
// GenerateForConditionHolds in src/elaborator/elaborator_generate.cpp gains for
// an expression it could not fold is also raised for one that folded to zero,
// which is the shape a fix takes when it reports at the site of the break
// rather than at the fold.
//
// The absence of a report is read here rather than through ReportedWarning in
// lib/cpp/test_helpers/helpers_reported_error.h, which answers that a named
// report was made and has no form for the claim that none was.
TEST(GenerateElaboration, GenerateForBoundThatFoldsToFalseIsNotReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  for (genvar i = 0; i < 0; i = i + 1) begin : g\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f);
  std::string reported;
  for (const auto& diag : f.diag.Diagnostics()) {
    if (diag.subclause != "27.4") continue;
    reported +=
        (diag.severity == DiagSeverity::kError ? "\n  error" : "\n  warning");
    reported += " at line " + std::to_string(diag.loc.line) + ": ";
    reported += diag.message;
  }
  EXPECT_EQ(reported, "")
      << "a loop generate whose bound folds to 0 is a legal "
         "zero-trip loop, and the run reported it under "
         "§27.4:"
      << reported;
}

// §27.3 gives genvar_iteration three forms -- an assignment_operator on the
// genvar, and ++ or -- before or after it -- so a third header position holding
// a bare identifier is no genvar_iteration and the source is illegal. §27.4
// says the same in prose: "Both the initialization and iteration assignments in
// the loop generate scheme shall assign to the same genvar", and `i` assigns to
// nothing. Name the report rather than count the instances, because a loop that
// elaborates once and a source that never parsed leave the same design behind.
TEST(GenerateElaboration, GenerateForStepThatIsAPlainIdentifierIsRejected) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 4; i) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-for iteration shall assign to a genvar",
                            4, "27.4"));
}

// §27.3: inc_or_dec_operator is ++ or -- and nothing else, so `~i` in the third
// header position is no genvar_iteration either. It reaches the rule by the
// other route: the step does name the genvar the initialization named, so the
// same-genvar check has nothing to object to and only the form is wrong.
TEST(GenerateElaboration, GenerateForStepThatIsANonIncrementUnaryIsRejected) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 4; ~i) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-for iteration shall assign to a genvar",
                            4, "27.4"));
}

}  // namespace
