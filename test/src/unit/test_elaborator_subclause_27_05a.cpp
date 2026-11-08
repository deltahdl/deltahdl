#include <gtest/gtest.h>

#include <set>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

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

TEST(GenerateElaboration, GenerateIfElseIfChainSelectsSecondElseIf) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames(FourAlternativeChain(2), f),
            (std::set<std::string>{"genblk1_alt_two"}));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block 'dup' has the same name as a "
                            "generate block in another generate construct",
                            2, "27.5"));
}

TEST(GenerateElaboration, BlockNameCollidesWithDeclarationIsError) {
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
      3, "27.5"));
}

TEST(GenerateElaboration, CaseBlockNameCollidesWithDeclarationIsError) {
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate block 'dup' conflicts with another declaration in the same "
      "scope",
      3, "27.5"));
}

TEST(GenerateElaboration, CaseAndIfBlockNameCollideAcrossConstructsIsError) {
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block 'shared' has the same name as a "
                            "generate block in another generate construct",
                            2, "27.5"));
}

TEST(GenerateElaboration, GenvarSelectsConditionalBranchPerIteration) {
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
  EXPECT_EQ(first_count, 1);
  EXPECT_EQ(rest_count, 2);
}

TEST(GenerateElaboration, BlockNameCollidesWithLoopGenerateIsError) {
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block 'shared' has the same name as a "
                            "generate block in another generate construct",
                            2, "27.5"));
}

TEST(GenerateElaboration, GenerateIfBodyWithoutBeginEnd) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top ();\n"
                                    "  if (1) logic [7:0] bare;\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"genblk1_bare"}));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-if condition is not constant", 8,
                            "27.5"));
}

TEST(GenerateElaboration, GenerateIfNonConstantElseIfConditionIsReported) {
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-if condition is not constant", 10,
                            "27.5"));
}

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
  const auto* x = FindVar(design, "b", "g_x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 8u);
}

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
  const auto* y = FindVar(design, "b", "g_y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->width, 2u);
}

TEST(GenerateElaboration, InstanceInTheSelectedBlockDeclaresItsBodysNames) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m2(input logic clk);\n"
      "  int p = 0, q = 0, n = 0;\n"
      "  int k;\n"
      "  initial k = 0;\n"
      "  always @(posedge clk) k <= k + p + q;\n"
      "  always_ff @(posedge clk) n <= n + 1;\n"
      "endmodule\n"
      "module top;\n"
      "  parameter P = 1;\n"
      "  logic clk = 0;\n"
      "  generate if (P == 1) begin : g\n"
      "    m2 c(clk);\n"
      "  end endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GenerateElaboration, MemberAGenerateBlockDoesNotDeclareIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  if (1) begin : g\n"
      "    int a;\n"
      "  end\n"
      "  initial $display(\"%0d\", g.nothere);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference 'g.nothere' is unresolved: "
                            "'nothere' is not declared in generate block 'g'",
                            5, "23.6"));
}

TEST(GenerateElaboration, MembersAGenerateBlockDeclaresAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf;\n"
      "  int v;\n"
      "endmodule\n"
      "module top;\n"
      "  if (1) begin : g\n"
      "    int a;\n"
      "    leaf u();\n"
      "    function int f();\n"
      "      return 1;\n"
      "    endfunction\n"
      "  end\n"
      "  for (genvar i = 0; i < 2; i++) begin : h\n"
      "    int b;\n"
      "  end\n"
      "  int x;\n"
      "  initial x = g.a + g.u.v + g.f() + h[0].i + h[1].b;\n"
      "endmodule\n",
      f);
  for (const auto& diag : f.diag.Diagnostics()) {
    EXPECT_EQ(diag.message.find("is not declared in generate block"),
              std::string::npos)
        << diag.message;
  }
}

}  // namespace
