#include <set>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

// Every name the variables of the elaborated source's top module carry.
//
// §27.5 instantiates "at most one" of the alternative generate blocks of a
// conditional generate construct, and §27.5 also rules that the selected block
// creates a scope whether or not it is named, so each declaration inside one
// reaches the flattened design under the block's name and its own. The whole
// set therefore states how many blocks were instantiated, which of them, and
// under what name, where a name-at-a-time scan states only that one expected
// name is present and leaves a second block free to be there too.
//
// An empty set is returned when the source produced no design, which no
// expectation below matches.
static std::set<std::string> ElaboratedVariableNames(const std::string& src,
                                                     ElabFixture& f) {
  auto* design = Elaborate(src, f);
  if (design == nullptr) return {};
  std::set<std::string> names;
  for (const auto& v : design->top_modules[0]->variables) {
    names.insert(std::string(v.name));
  }
  return names;
}

// §27.6 names an unnamed generate block genblk<n> after the number of its
// enclosing generate construct, and both alternatives of one if-generate belong
// to one construct, so the then-block and the else-block of the single
// construct here are both genblk1.
TEST(GenerateElaboration, GenerateIfTrueSelectsThenBranch) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top #(parameter W = 16) ();\n"
                                    "  if (W > 8) begin\n"
                                    "    logic [15:0] wide_bus;\n"
                                    "  end else begin\n"
                                    "    logic [7:0] narrow_bus;\n"
                                    "  end\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"genblk1_wide_bus"}));
}

TEST(GenerateElaboration, GenerateIfFalseSelectsElseBranch) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top #(parameter W = 4) ();\n"
                                    "  if (W > 8) begin\n"
                                    "    logic [15:0] wide_bus;\n"
                                    "  end else begin\n"
                                    "    logic [7:0] narrow_bus;\n"
                                    "  end\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"genblk1_narrow_bus"}));
}

// §27.6 assigns one number to the whole case-generate construct, so every
// alternative of the one construct here is genblk1.
TEST(GenerateElaboration, GenerateCaseMatchesPattern) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top #(parameter SEL = 1) ();\n"
                                    "  case (SEL)\n"
                                    "    0: logic [7:0] bus0;\n"
                                    "    1: logic [15:0] bus1;\n"
                                    "    default: logic [31:0] bus_def;\n"
                                    "  endcase\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"genblk1_bus1"}));
}

TEST(GenerateElaboration, GenerateCaseSelectsDefault) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top #(parameter SEL = 99) ();\n"
                                    "  case (SEL)\n"
                                    "    0: logic [7:0] bus0;\n"
                                    "    1: logic [15:0] bus1;\n"
                                    "    default: logic [31:0] bus_def;\n"
                                    "  endcase\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"genblk1_bus_def"}));
}

// The empty set rather than the absence of one name: an if-generate whose
// condition is false and which has no else instantiates nothing at all, so
// naming genblk1_guarded here would leave a case that passes on any other name
// the elaborator might spell.
TEST(GenerateElaboration, GenerateIfFalseNoElse) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top #(parameter EN = 0) ();\n"
                                    "  if (EN) begin\n"
                                    "    logic [7:0] guarded;\n"
                                    "  end\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{}));
}

TEST(GenerateElaboration, GenerateCaseNoMatchNoDefault) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top #(parameter SEL = 5) ();\n"
                                    "  case (SEL)\n"
                                    "    0: logic [7:0] bus0;\n"
                                    "    1: logic [15:0] bus1;\n"
                                    "  endcase\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{}));
}

TEST(GenerateElaboration, GenerateIfTrueNoElse) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top #(parameter EN = 1) ();\n"
                                    "  if (EN) begin\n"
                                    "    logic [7:0] enabled;\n"
                                    "  end\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"genblk1_enabled"}));
}

// §27.5: the block an `else if` stands in "consists of only one item that is
// itself a conditional generate construct" and is not surrounded by begin-end,
// so it is directly nested and "the generate blocks of the directly nested
// construct are treated as if they belong to the outer construct". Every
// alternative of the chain therefore carries the outer construct's number,
// genblk1, rather than a number of its own.
TEST(GenerateElaboration, GenerateIfElseIfChainSelectsMiddle) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top #(parameter SEL = 1) ();\n"
                                    "  if (SEL == 0) begin\n"
                                    "    logic [7:0] zero;\n"
                                    "  end else if (SEL == 1) begin\n"
                                    "    logic [7:0] one;\n"
                                    "  end else begin\n"
                                    "    logic [7:0] other;\n"
                                    "  end\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"genblk1_one"}));
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
  EXPECT_EQ(ElaboratedVariableNames("module top #(parameter SEL = 2) ();\n"
                                    "  if (SEL == 0) begin\n"
                                    "    logic [7:0] zero;\n"
                                    "  end else if (SEL == 1) begin\n"
                                    "    logic [7:0] one;\n"
                                    "  end else begin\n"
                                    "    logic [7:0] other;\n"
                                    "  end\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"genblk1_other"}));
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

// §27.5: selecting the second `else if` needs both the first `else if`
// condition evaluated and answered false and the second evaluated and answered
// true. Reaching the else branch only one step deep yields alt_one instead.
// The chain is one construct for §27.6 numbering, since each `else if` is
// directly nested in the alternative before it, so every alternative's block is
// genblk1.
TEST(GenerateElaboration, GenerateIfElseIfChainSelectsSecondElseIf) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames(FourAlternativeChain(2), f),
            (std::set<std::string>{"genblk1_alt_two"}));
}

// §27.5: the final else of a four-alternative chain is reached only after both
// `else if` conditions have been evaluated and both answered false.
TEST(GenerateElaboration,
     GenerateIfElseIfChainSelectsFinalElseOfFourAlternatives) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames(FourAlternativeChain(3), f),
            (std::set<std::string>{"genblk1_alt_last"}));
}

TEST(GenerateElaboration, GenerateCaseMultiplePatternsPerItem) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top #(parameter SEL = 2) ();\n"
                                    "  case (SEL)\n"
                                    "    0, 1, 2: logic [7:0] early;\n"
                                    "    default: logic [7:0] late;\n"
                                    "  endcase\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"genblk1_early"}));
}

TEST(GenerateElaboration, GenerateIfSelectsOnLocalparam) {
  // §27.5: the selecting constant expression is evaluated during elaboration.
  // A localparam is a valid constant form for it and resolves through a
  // different path than a header parameter (its value is fixed by a body
  // declaration), so the if-generate must select against the resolved
  // localparam value.
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top ();\n"
                                    "  localparam MODE = 1;\n"
                                    "  if (MODE == 1) begin\n"
                                    "    logic sel_then;\n"
                                    "  end else begin\n"
                                    "    logic sel_else;\n"
                                    "  end\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"genblk1_sel_then"}));
}

TEST(GenerateElaboration, GenerateCaseSelectsOnLocalparam) {
  // §27.5: a case-generate selector may likewise be a localparam constant,
  // selecting the matching item at elaboration.
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top ();\n"
                                    "  localparam SEL = 2;\n"
                                    "  case (SEL)\n"
                                    "    1: logic [7:0] one;\n"
                                    "    2: logic [7:0] two;\n"
                                    "    default: logic [7:0] def;\n"
                                    "  endcase\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"genblk1_two"}));
}

TEST(GenerateElaboration, GenerateCaseSelectsOnLiteralSelector) {
  // §27.5: the case-generate selector may be a plain literal constant, chosen
  // at elaboration with no parameter or localparam involved.
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top ();\n"
                                    "  case (3)\n"
                                    "    1: logic [7:0] one;\n"
                                    "    3: logic [7:0] three;\n"
                                    "    default: logic [7:0] def;\n"
                                    "  endcase\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"genblk1_three"}));
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

// §27.5: a generate block "may consist of only one item, which need not be
// surrounded by begin-end keywords. Even if the begin-end keywords are absent,
// it is still a generate block, which, like all generate blocks, comprises a
// separate scope". The single item here is a variable declaration rather than a
// conditional generate construct, so the direct-nesting exception does not
// apply and the block is a scope, named genblk1 by §27.6.
TEST(GenerateElaboration, GenerateIfBodyWithoutBeginEnd) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top ();\n"
                                    "  if (1) logic [7:0] bare;\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"genblk1_bare"}));
}

// §27.5: "If the generate block selected for instantiation is named, then this
// name declares a generate block instance and is the name for the scope it
// creates." Two if-generate constructs whose conditions are both true
// instantiate two blocks, and the two scopes are what let each declare v. Both
// declarations landing in the module's own scope made the second a
// redeclaration of the first, so this source was rejected.
TEST(GenerateElaboration, SiblingNamedIfBlocksDeclareTheSameSimpleName) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top ();\n"
                                    "  if (1) begin : lo\n"
                                    "    logic v;\n"
                                    "  end\n"
                                    "  if (1) begin : hi\n"
                                    "    logic v;\n"
                                    "  end\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"lo_v", "hi_v"}));
  EXPECT_FALSE(f.has_errors);
}

// §27.5: "If the generate block selected for instantiation is not named, it
// still creates a scope." §27.6 numbers the generate constructs of a scope from
// 1 in textual order, so the two constructs here are 1 and 2 and their blocks
// are genblk1 and genblk2. This is the case that says the numbering runs over
// constructs rather than over blocks: one number for both would put the two
// declarations back in one scope.
TEST(GenerateElaboration, SiblingUnnamedIfBlocksAreNumberedInOrder) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top ();\n"
                                    "  if (1) begin\n"
                                    "    logic v;\n"
                                    "  end\n"
                                    "  if (1) begin\n"
                                    "    logic v;\n"
                                    "  end\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"genblk1_v", "genblk2_v"}));
  EXPECT_FALSE(f.has_errors);
}

// §27.5 puts the block's declarations in the scope the block creates, which is
// not the module's scope, so a module-level declaration and a block-level one
// may carry the same simple name. §27.5 forbids the block's own name colliding
// with another declaration in the same scope, which
// GenerateElaboration.BlockNameCollidesWithDeclarationIsError above covers, and
// the block here is named g rather than v.
TEST(GenerateElaboration,
     IfBlockDeclarationDoesNotCollideWithModuleLevelDeclaration) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top ();\n"
                                    "  logic v;\n"
                                    "  if (1) begin : g\n"
                                    "    logic v;\n"
                                    "  end\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"v", "g_v"}));
  EXPECT_FALSE(f.has_errors);
}

// §27.5: the outer block "consists of only one item that is itself a
// conditional generate construct" and that item "is not surrounded by
// begin-end keywords", so the outer block "is not treated as a separate scope"
// and contributes no name of its own. inner_v rather than genblk1_inner_v is
// the whole claim, since the extra component would be a level of generate block
// hierarchy §27.5 rules out.
TEST(GenerateElaboration, DirectlyNestedIfContributesNoScope) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top ();\n"
                                    "  if (1) if (1) begin : inner\n"
                                    "    logic v;\n"
                                    "  end\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"inner_v"}));
}

// The other half of the pair above, and the source differs from it only in the
// begin-end around the outer block. §27.5 conditions direct nesting on that
// item not being surrounded by begin-end, so the outer block is an ordinary
// scope here, named genblk1 by §27.6, and the declaration carries both
// components. Read together, the two cases say direct nesting is decided by the
// begin-end rather than assumed either way.
TEST(GenerateElaboration, BeginEndAroundNestedIfContributesAScope) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top ();\n"
                                    "  if (1) begin\n"
                                    "    if (1) begin : inner\n"
                                    "      logic v;\n"
                                    "    end\n"
                                    "  end\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"genblk1_inner_v"}));
}

// §27.5 names the scope after the block selected for instantiation, and the
// block a case-generate selects is the one labelling the matching alternative,
// so the prefix is that alternative's own label and not the label of any other
// alternative of the construct.
TEST(GenerateElaboration, CaseAlternativeLabelPrefixesItsDeclaration) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top #(parameter SEL = 1) ();\n"
                                    "  case (SEL)\n"
                                    "    1: begin : one_alt\n"
                                    "      logic v;\n"
                                    "    end\n"
                                    "    default: begin : def_alt\n"
                                    "      logic v;\n"
                                    "    end\n"
                                    "  endcase\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"one_alt_v"}));
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
  // §27.5 makes the named block g a scope, so the declaration inside it is
  // g_x rather than x.
  const auto* x = FindVar(design, "b", "g_x");
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
  // b's y is declared inside the named block g, which §27.5 makes a scope.
  const auto* y = FindVar(design, "b", "g_y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->width, 2u);
}

}  // namespace
