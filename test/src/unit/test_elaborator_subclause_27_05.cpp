#include <set>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(GenerateElaboration, GenerateIfTrueSelectsThenBranch) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter W = 16) ();\n"
      "  if (W > 8) begin\n"
      "    logic [15:0] wide_bus;\n"
      "  end else begin\n"
      "    logic [7:0] narrow_bus;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_wide = false;
  for (const auto& v : mod->variables) {
    if (v.name == "wide_bus") found_wide = true;
  }
  EXPECT_TRUE(found_wide);
}

TEST(GenerateElaboration, GenerateIfFalseSelectsElseBranch) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter W = 4) ();\n"
      "  if (W > 8) begin\n"
      "    logic [15:0] wide_bus;\n"
      "  end else begin\n"
      "    logic [7:0] narrow_bus;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_narrow = false;
  for (const auto& v : mod->variables) {
    if (v.name == "narrow_bus") found_narrow = true;
  }
  EXPECT_TRUE(found_narrow);
}

TEST(GenerateElaboration, GenerateCaseMatchesPattern) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter SEL = 1) ();\n"
      "  case (SEL)\n"
      "    0: logic [7:0] bus0;\n"
      "    1: logic [15:0] bus1;\n"
      "    default: logic [31:0] bus_def;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_bus1 = false;
  for (const auto& v : mod->variables) {
    if (v.name == "bus1") found_bus1 = true;
  }
  EXPECT_TRUE(found_bus1);
}

TEST(GenerateElaboration, GenerateCaseSelectsDefault) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter SEL = 99) ();\n"
      "  case (SEL)\n"
      "    0: logic [7:0] bus0;\n"
      "    1: logic [15:0] bus1;\n"
      "    default: logic [31:0] bus_def;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_def = false;
  for (const auto& v : mod->variables) {
    if (v.name == "bus_def") found_def = true;
  }
  EXPECT_TRUE(found_def);
}

TEST(GenerateElaboration, GenerateIfFalseNoElse) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter EN = 0) ();\n"
      "  if (EN) begin\n"
      "    logic [7:0] guarded;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  for (const auto& v : mod->variables) {
    EXPECT_NE(v.name, "guarded");
  }
}

TEST(GenerateElaboration, GenerateCaseNoMatchNoDefault) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter SEL = 5) ();\n"
      "  case (SEL)\n"
      "    0: logic [7:0] bus0;\n"
      "    1: logic [15:0] bus1;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 0u);
}

TEST(GenerateElaboration, GenerateIfTrueNoElse) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter EN = 1) ();\n"
      "  if (EN) begin\n"
      "    logic [7:0] enabled;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "enabled") found = true;
  }
  EXPECT_TRUE(found);
}

TEST(GenerateElaboration, GenerateIfElseIfChainSelectsMiddle) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter SEL = 1) ();\n"
      "  if (SEL == 0) begin\n"
      "    logic [7:0] zero;\n"
      "  end else if (SEL == 1) begin\n"
      "    logic [7:0] one;\n"
      "  end else begin\n"
      "    logic [7:0] other;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_zero = false, found_one = false, found_other = false;
  for (const auto& v : mod->variables) {
    if (v.name == "zero") found_zero = true;
    if (v.name == "one") found_one = true;
    if (v.name == "other") found_other = true;
  }
  EXPECT_FALSE(found_zero);
  EXPECT_TRUE(found_one);
  EXPECT_FALSE(found_other);
}

// §27.5 selects "at most one generate block from a set of alternative generate
// blocks based on constant expressions evaluated during elaboration", and an
// `else if` puts one of those constant expressions on the else branch. The four
// cases below fix SEL at values that only the alternative past the first
// `else if` answers, which is what GenerateIfElseIfChainSelectsMiddle above
// cannot do: SEL = 1 there selects the first `else if`, the one alternative
// reached whether the nested condition is evaluated or ignored.
//
// Elaborator::ElaborateGenerateIf in src/elaborator/elaborator_generate.cpp
// elaborated item->gen_else->gen_body for every else branch, and
// Parser::ParseGenerateIf at src/parser/parser_generate.cpp:181-182 makes
// gen_else the nested kGenerateIf itself for an `else if`, so that body was the
// nested construct's then-branch. Every chain therefore instantiated its first
// `else if` block whenever the leading condition was false, and no alternative
// past it -- including the final else -- was reachable at all.
TEST(GenerateElaboration, GenerateIfElseIfChainSelectsFinalElse) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter SEL = 2) ();\n"
      "  if (SEL == 0) begin\n"
      "    logic [7:0] zero;\n"
      "  end else if (SEL == 1) begin\n"
      "    logic [7:0] one;\n"
      "  end else begin\n"
      "    logic [7:0] other;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_zero = false, found_one = false, found_other = false;
  for (const auto& v : mod->variables) {
    if (v.name == "zero") found_zero = true;
    if (v.name == "one") found_one = true;
    if (v.name == "other") found_other = true;
  }
  EXPECT_TRUE(found_other);
  EXPECT_FALSE(found_zero);
  EXPECT_FALSE(found_one);
}

// A chain of four alternatives, each declaring one variable, for the selector
// given. Four puts a second `else if` past the first, so which one is selected
// says whether the else branch is followed as far as its own condition or only
// one step.
//
// Built here rather than written out per case because `pmd cpd
// --minimum-tokens 100`, which the copy-paste-test job runs over test/src/,
// reports a run repeated at that length, and two copies of this source are
// already 112 tokens.
static std::string FourAlternativeChain(int sel) {
  return "module top #(parameter SEL = " + std::to_string(sel) +
         ") ();\n"
         "  if (SEL == 0) begin\n"
         "    logic [7:0] alt_zero;\n"
         "  end else if (SEL == 1) begin\n"
         "    logic [7:0] alt_one;\n"
         "  end else if (SEL == 2) begin\n"
         "    logic [7:0] alt_two;\n"
         "  end else begin\n"
         "    logic [7:0] alt_last;\n"
         "  end\n"
         "endmodule\n";
}

// Every name the elaborated module's variables carry. §27.5 instantiates "at
// most one" of the alternative generate blocks and each alternative declares
// one variable, so the whole set states both how many blocks were instantiated
// and which, where a name-at-a-time scan states only that the expected one is
// present and leaves a second block free to be there too.
static std::set<std::string> VariableNames(const RtlirModule* mod) {
  std::set<std::string> names;
  for (const auto& v : mod->variables) names.insert(std::string(v.name));
  return names;
}

// §27.5: selecting the second `else if` needs both the first `else if`
// condition evaluated and answered false and the second evaluated and answered
// true. Reaching the else branch only one step deep yields alt_one instead.
TEST(GenerateElaboration, GenerateIfElseIfChainSelectsSecondElseIf) {
  ElabFixture f;
  auto* design = Elaborate(FourAlternativeChain(2), f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(VariableNames(mod), (std::set<std::string>{"alt_two"}));
}

// §27.5: the final else of a four-alternative chain is reached only after both
// `else if` conditions have been evaluated and both answered false.
TEST(GenerateElaboration,
     GenerateIfElseIfChainSelectsFinalElseOfFourAlternatives) {
  ElabFixture f;
  auto* design = Elaborate(FourAlternativeChain(3), f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(VariableNames(mod), (std::set<std::string>{"alt_last"}));
}

TEST(GenerateElaboration, GenerateCaseMultiplePatternsPerItem) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter SEL = 2) ();\n"
      "  case (SEL)\n"
      "    0, 1, 2: logic [7:0] early;\n"
      "    default: logic [7:0] late;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_early = false, found_late = false;
  for (const auto& v : mod->variables) {
    if (v.name == "early") found_early = true;
    if (v.name == "late") found_late = true;
  }
  EXPECT_TRUE(found_early);
  EXPECT_FALSE(found_late);
}

TEST(GenerateElaboration, GenerateIfSelectsOnLocalparam) {
  // §27.5: the selecting constant expression is evaluated during elaboration.
  // A localparam is a valid constant form for it and resolves through a
  // different path than a header parameter (its value is fixed by a body
  // declaration), so the if-generate must select against the resolved
  // localparam value.
  ElabFixture f;
  auto* design = Elaborate(
      "module top ();\n"
      "  localparam MODE = 1;\n"
      "  if (MODE == 1) begin\n"
      "    logic sel_then;\n"
      "  end else begin\n"
      "    logic sel_else;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_then = false, found_else = false;
  for (const auto& v : mod->variables) {
    if (v.name == "sel_then") found_then = true;
    if (v.name == "sel_else") found_else = true;
  }
  EXPECT_TRUE(found_then);
  EXPECT_FALSE(found_else);
}

TEST(GenerateElaboration, GenerateCaseSelectsOnLocalparam) {
  // §27.5: a case-generate selector may likewise be a localparam constant,
  // selecting the matching item at elaboration.
  ElabFixture f;
  auto* design = Elaborate(
      "module top ();\n"
      "  localparam SEL = 2;\n"
      "  case (SEL)\n"
      "    1: logic [7:0] one;\n"
      "    2: logic [7:0] two;\n"
      "    default: logic [7:0] def;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_two = false, found_one = false, found_def = false;
  for (const auto& v : mod->variables) {
    if (v.name == "one") found_one = true;
    if (v.name == "two") found_two = true;
    if (v.name == "def") found_def = true;
  }
  EXPECT_TRUE(found_two);
  EXPECT_FALSE(found_one);
  EXPECT_FALSE(found_def);
}

TEST(GenerateElaboration, GenerateCaseSelectsOnLiteralSelector) {
  // §27.5: the case-generate selector may be a plain literal constant, chosen
  // at elaboration with no parameter or localparam involved.
  ElabFixture f;
  auto* design = Elaborate(
      "module top ();\n"
      "  case (3)\n"
      "    1: logic [7:0] one;\n"
      "    3: logic [7:0] three;\n"
      "    default: logic [7:0] def;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_three = false, found_one = false, found_def = false;
  for (const auto& v : mod->variables) {
    if (v.name == "one") found_one = true;
    if (v.name == "three") found_three = true;
    if (v.name == "def") found_def = true;
  }
  EXPECT_TRUE(found_three);
  EXPECT_FALSE(found_one);
  EXPECT_FALSE(found_def);
}

TEST(GenerateElaboration, SameNamedBlocksAcrossAlternativesAllowed) {
  // §27.5: because at most one alternative of a conditional generate construct
  // is instantiated, more than one block within a single construct may carry
  // the same name.
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter P = 1) ();\n"
      "  if (P == 1) begin : u1\n"
      "    logic a;\n"
      "  end else if (P == 2) begin : u1\n"
      "    logic b;\n"
      "  end else begin : u1\n"
      "    logic c;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GenerateElaboration, SameNamedBlocksAcrossAlternativesAllowedCase) {
  // §27.5: the same allowance applies to a case-generate construct.
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter SEL = 0) ();\n"
      "  case (SEL)\n"
      "    0: begin : u1 logic a; end\n"
      "    1: begin : u1 logic b; end\n"
      "    default: begin : u1 logic c; end\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GenerateElaboration, BlockNameCollidesAcrossConstructsIsError) {
  // §27.5: a named generate block must not share its name with a generate block
  // in another generate construct in the same scope, even if neither block is
  // selected for instantiation.
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 1) ();\n"
      "  if (P) begin : dup\n"
      "    logic a;\n"
      "  end\n"
      "  if (!P) begin : dup\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n",
      f);
  // The report stands at the first if-generate (line 2), which is where the
  // construct that claims the name begins; the second construct draws its own
  // copy of the same report at line 5.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block 'dup' has the same name as a "
                            "generate block in another generate construct",
                            2, "23.9"));
}

TEST(GenerateElaboration, BlockNameCollidesWithDeclarationIsError) {
  // §27.5: a named generate block must not share its name with any other
  // declaration in the same scope.
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 1) ();\n"
      "  logic dup;\n"
      "  if (P) begin : dup\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate block 'dup' conflicts with another declaration in the same "
      "scope",
      3, "23.9"));
}

TEST(GenerateElaboration, CaseBlockNameCollidesWithDeclarationIsError) {
  // §27.5: the same-scope naming rule also covers case-generate alternatives --
  // a case item's block name must not collide with another declaration.
  ElabFixture f;
  Elaborate(
      "module top #(parameter SEL = 0) ();\n"
      "  logic dup;\n"
      "  case (SEL)\n"
      "    0: begin : dup logic a; end\n"
      "    default: begin : other logic b; end\n"
      "  endcase\n"
      "endmodule\n",
      f);
  // The case-generate is one construct, so its report stands at the `case`
  // keyword on line 3 rather than at the offending case item on line 4.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate block 'dup' conflicts with another declaration in the same "
      "scope",
      3, "23.9"));
}

TEST(GenerateElaboration, CaseAndIfBlockNameCollideAcrossConstructsIsError) {
  // §27.5: a case-generate block and an if-generate block in separate
  // constructs in the same scope may not share a name.
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 1) ();\n"
      "  if (P) begin : shared\n"
      "    logic a;\n"
      "  end\n"
      "  case (P)\n"
      "    1: begin : shared logic b; end\n"
      "  endcase\n"
      "endmodule\n",
      f);
  // Both constructs draw the report; this names the if-generate's copy, at the
  // `if` on line 2.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block 'shared' has the same name as a "
                            "generate block in another generate construct",
                            2, "23.9"));
}

TEST(GenerateElaboration, GenvarSelectsConditionalBranchPerIteration) {
  // §27.5: the selecting constant expression of a conditional generate is
  // evaluated during elaboration. When the conditional generate is nested in a
  // loop generate (§27.4), the loop genvar is a valid constant form for that
  // expression, so each iteration can select a different alternative. Here the
  // first iteration takes the then-branch and the remaining iterations take the
  // else-branch, proving selection is re-evaluated against the per-iteration
  // genvar value rather than fixed once.
  ElabFixture f;
  auto* design = Elaborate(
      "module top ();\n"
      "  for (genvar i = 0; i < 3; i = i + 1) begin : g\n"
      "    if (i == 0) begin\n"
      "      logic first_only;\n"
      "    end else begin\n"
      "      logic rest_block;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  int first_count = 0, rest_count = 0;
  for (const auto& v : mod->variables) {
    if (v.name.find("first_only") != std::string_view::npos) ++first_count;
    if (v.name.find("rest_block") != std::string_view::npos) ++rest_count;
  }
  EXPECT_EQ(first_count, 1);  // only the i==0 iteration
  EXPECT_EQ(rest_count, 2);   // the i==1 and i==2 iterations
}

TEST(GenerateElaboration, BlockNameCollidesWithLoopGenerateIsError) {
  // §27.5: the prohibition on sharing a block name across generate constructs
  // in the same scope covers loop generate constructs as well -- a conditional
  // generate block may not reuse the array name of a loop generate construct,
  // even though neither block is selected for instantiation together.
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 1) ();\n"
      "  if (P) begin : shared\n"
      "    logic a;\n"
      "  end\n"
      "  for (genvar i = 0; i < 2; i = i + 1) begin : shared\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n",
      f);
  // Elaborator::CheckConditionalGenerateNaming reports only for the
  // conditional construct, so the report stands at the `if` on line 2 even
  // though the loop generate is the other half of the collision.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block 'shared' has the same name as a "
                            "generate block in another generate construct",
                            2, "23.9"));
}

TEST(GenerateElaboration, GenerateIfBodyWithoutBeginEnd) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top ();\n"
      "  if (1) logic [7:0] bare;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "bare") found = true;
  }
  EXPECT_TRUE(found);
}

// §27.5 selects a conditional generate block "based on constant expressions
// evaluated during elaboration", and §26.3 makes a wildcard-imported name
// locally visible only "prior to that point within the current scope". The
// scope holding the import here is module a, so W names nothing in module b and
// the condition is not a constant expression there:
// Elaborator::ElaborateGenerateIf in src/elaborator/elaborator_generate.cpp
// warns and instantiates neither branch.
//
// What this fails on is the condition folding anyway, which it does when the
// scope the condition is evaluated against is assembled after every module has
// been elaborated rather than inside module b. The report is what the case
// names rather than the absence of b.g, because a source that never parsed
// leaves b.g out of the design just as surely.
//
// Both modules have to be elaborated for the question to arise, which is what
// the auto_top argument asks for: with a single named top, module a is never
// elaborated and there is nothing for module b to pick up.
TEST(GenerateElaboration,
     ImportedParameterDoesNotReachAnotherModulesGenerateIf) {
  ElabFixture f;
  ElaborateWithPreprocessor(
      "package p;\n"
      "  parameter int W = 1;\n"
      "endpackage\n"
      "module a;\n"
      "  import p::*;\n"
      "endmodule\n"
      "module b;\n"
      "  if (W == 1) begin : g\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f, "", true);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "generate-if condition is not constant", 8,
                              "27.5"));
}

// §27.5 requires every alternative of a conditional generate construct to be
// selected on a constant expression, and the condition an `else if` carries is
// one of them, so a non-constant one there is reported exactly as a
// non-constant leading condition is. The source is the one above -- W is
// imported by module a and so names nothing in module b, per §26.3 -- with the
// non-constant condition moved onto the else branch behind a leading `if (0)`
// that folds. Elaborator::ElaborateGenerateIf reaches it by recursing into
// item->gen_else, and the report stands at the nested `if` on line 10 because
// Parser::ParseGenerateIf takes that node's loc at the `if` token
// (src/parser/parser_generate.cpp:172) after consuming the `else`.
//
// What this fails on is the else branch being instantiated without its
// condition read, which produced no report at all and built g1 regardless of W.
TEST(GenerateElaboration, GenerateIfNonConstantElseIfConditionIsWarned) {
  ElabFixture f;
  ElaborateWithPreprocessor(
      "package p;\n"
      "  parameter int W = 1;\n"
      "endpackage\n"
      "module a;\n"
      "  import p::*;\n"
      "endmodule\n"
      "module b;\n"
      "  if (0) begin : g0\n"
      "    logic y;\n"
      "  end else if (W == 1) begin : g1\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f, "", true);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "generate-if condition is not constant", 10,
                              "27.5"));
}

// The other side of §26.3: the import that module b writes is in force for
// module b, so W is a constant expression in b's own generate-if and §27.5
// selects the then-branch on it. This is what fails if the scope a pending
// generate is evaluated against loses the imports of the module the generate
// was written in, rather than only the imports of the other modules.
//
// The width is 8 rather than 1 because W resolved twice: once in the condition
// that selected the block, and once in the range bound of the declaration
// inside it. EvalRangeWidth in src/elaborator/type_eval.cpp answers 0 for a
// bound it cannot fold and the declaration falls back to DataTypeKind::kLogic,
// one bit, so 1 would say the block was instantiated with W unresolved.
TEST(GenerateElaboration, ImportedParameterReachesItsOwnModulesGenerateIf) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "package p;\n"
      "  parameter int W = 8;\n"
      "endpackage\n"
      "module a;\n"
      "endmodule\n"
      "module b;\n"
      "  import p::*;\n"
      "  if (W == 8) begin : g\n"
      "    logic [W-1:0] x;\n"
      "  end\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  const auto* x = FindVar(design, "b", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 8u);
}

// §26.3 covers the type identifier an import carries as well as the parameter,
// and a generate block "comprises a separate scope and a new level of
// hierarchy" (§27.4) inside the module that wrote it, so a declaration in
// module b's generate block is sized by what module b can see. word_t is
// imported by module a alone, so b's y has to be left unsized.
//
// The localparam gating the block is declared by module b, which is what
// separates this from the two cases above: the condition folds either way, so
// what the case fails on is the type identifier reaching the block's body.
//
// 16 on a's x says the import still reaches the module that wrote it, so the
// case cannot pass by resolving no typedef anywhere. 2 on b's y says word_t
// reached b's generate block as an ordinary name: A.10.3 lets a parameter
// declaration leave its data type implicit, so `localparam word_t = 1;` names
// word_t where word_t is not a type, and gives word_t as the type of a
// parameter with no name where it is, which no parse accepts. The width then
// says the block was elaborated and its parameter folded rather than that the
// block was dropped.
//
// The block declared `word_t y;` until Parser::ParsePackageDecl in
// src/parser/parser.cpp began scoping a package's type names. §6.18 requires a
// type identifier to be declared, so that declaration was illegal and this case
// asserted the width the elaborator happened to leave on it.
TEST(GenerateElaboration,
     ImportedTypedefDoesNotSizeAnotherModulesGenerateBlock) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "package p;\n"
      "  typedef logic [15:0] word_t;\n"
      "endpackage\n"
      "module a;\n"
      "  import p::*;\n"
      "  word_t x;\n"
      "endmodule\n"
      "module b;\n"
      "  localparam EN = 1;\n"
      "  if (EN == 1) begin : g\n"
      "    localparam word_t = 1;\n"
      "    logic [word_t:0] y;\n"
      "  end\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* x = FindVar(design, "a", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 16u);
  const auto* y = FindVar(design, "b", "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->width, 2u);
}

}  // namespace
