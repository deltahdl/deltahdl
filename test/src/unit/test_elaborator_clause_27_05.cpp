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
