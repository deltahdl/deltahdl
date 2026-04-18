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

TEST(GenerateElaboration, IfGenerateElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int P = 1;\n"
             "  if (P) begin : gen\n"
             "    logic w;\n"
             "  end\n"
             "endmodule\n"));
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

// §27.5: else binds to the nearest preceding if, so the middle arm of an
// if / else-if / else chain is taken when its condition is the first to hold.
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

// §27.5: a case-generate item with a comma-separated list of constant
// expressions selects its body when any pattern equals the controlling value.
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

// §27.5: the generate_block body may be a single generate_item with no
// surrounding begin/end.
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
