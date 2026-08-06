#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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

}  // namespace
