#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_generate_elab.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(GenerateBlockNaming, FirstUnnamedConstructIsGenblk1) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (1) begin\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->items.size(), 1u);
  EXPECT_EQ(m->items[0]->kind, ModuleItemKind::kGenerateIf);
  EXPECT_EQ(m->items[0]->name, "genblk1");
}

TEST(GenerateBlockNaming, SecondUnnamedConstructIsGenblk2) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (1) begin\n"
      "    logic a;\n"
      "  end\n"
      "  if (1) begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->items.size(), 2u);
  EXPECT_EQ(m->items[0]->name, "genblk1");
  EXPECT_EQ(m->items[1]->name, "genblk2");
}

// §27.6: only generate constructs are counted. An ordinary declaration sitting
// between two generate constructs does not consume a number, so the second
// construct is genblk2 (not genblk3) despite the intervening item.
TEST(GenerateBlockNaming, NonGenerateItemsDoNotConsumeNumbers) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (1) begin\n"
      "    logic a;\n"
      "  end\n"
      "  logic mid;\n"
      "  if (1) begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  ExpectFirstTwoGenerateIfNames(*r.cu->modules[0], "genblk1", "genblk2");
}

TEST(GenerateBlockNaming, ExplicitLabelIsRetained) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (1) begin : my_block\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->items.size(), 1u);
  EXPECT_EQ(m->items[0]->name, "my_block");
}

TEST(GenerateBlockNaming, NumberingCountsNamedConstructs) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (1) begin : first\n"
      "    logic a;\n"
      "  end\n"
      "  if (1) begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->items.size(), 2u);
  EXPECT_EQ(m->items[0]->name, "first");

  EXPECT_EQ(m->items[1]->name, "genblk2");
}

TEST(GenerateBlockNaming, CollisionResolvedByLeadingZero) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter genblk2 = 0;\n"
      "  if (1) begin\n"
      "    logic a;\n"
      "  end\n"
      "  if (1) begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  ExpectFirstTwoGenerateIfNames(*r.cu->modules[0], "genblk1", "genblk02");
}

// §27.6: the naming scheme applies to every generate construct, not just the
// if-generate. An unnamed loop generate is numbered and named genblk<n> the
// same way (the LRM example's genblk4 is an unnamed for-generate).
TEST(GenerateBlockNaming, UnnamedForGenerateGetsGenblkName) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  for (genvar i = 0; i < 2; i = i + 1) begin\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->items.size(), 1u);
  EXPECT_EQ(m->items[0]->kind, ModuleItemKind::kGenerateFor);
  EXPECT_EQ(m->items[0]->name, "genblk1");
}

// §27.6: the running number spans generate constructs of different kinds in the
// same scope -- an if-generate followed by a for-generate is numbered 1 then 2.
TEST(GenerateBlockNaming, MixedConstructKindsNumberSequentially) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (1) begin\n"
      "    logic a;\n"
      "  end\n"
      "  for (genvar i = 0; i < 2; i = i + 1) begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->items.size(), 2u);
  EXPECT_EQ(m->items[0]->kind, ModuleItemKind::kGenerateIf);
  EXPECT_EQ(m->items[0]->name, "genblk1");
  EXPECT_EQ(m->items[1]->kind, ModuleItemKind::kGenerateFor);
  EXPECT_EQ(m->items[1]->name, "genblk2");
}

// §27.6: the naming scheme applies to a case generate construct too. An
// unnamed case-generate is numbered and named genblk<n> like the if and for
// forms (the third generate-construct kind).
TEST(GenerateBlockNaming, UnnamedCaseGenerateGetsGenblkName) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  case (1)\n"
      "    1: begin\n"
      "      logic a;\n"
      "    end\n"
      "    default: begin\n"
      "      logic b;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->items.size(), 1u);
  EXPECT_EQ(m->items[0]->kind, ModuleItemKind::kGenerateCase);
  EXPECT_EQ(m->items[0]->name, "genblk1");
}

// §27.6: the conflicting "explicitly declared name" is any declaration in the
// scope, not only a parameter. A net/variable named genblk1 forces the first
// unnamed construct to genblk01 -- the same leading-zero resolution driven by a
// declaration collected through a different path than the parameter case.
TEST(GenerateBlockNaming, NameConflictWithDeclaredNetResolvedByLeadingZero) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  logic genblk1;\n"
      "  if (1) begin\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* m = r.cu->modules[0];
  ModuleItem* gen = nullptr;
  for (auto* it : m->items) {
    if (it->kind == ModuleItemKind::kGenerateIf) gen = it;
  }
  ASSERT_NE(gen, nullptr);
  EXPECT_EQ(gen->name, "genblk01");
}

// §27.6: leading zeros keep being prepended until the generated name no
// longer clashes. When both genblk2 and genblk02 are already taken, the
// second construct must fall through to genblk002.
TEST(GenerateBlockNaming, RepeatedCollisionAddsMoreLeadingZeros) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter genblk2 = 0;\n"
      "  parameter genblk02 = 0;\n"
      "  if (1) begin\n"
      "    logic a;\n"
      "  end\n"
      "  if (1) begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* m = r.cu->modules[0];
  ModuleItem* second = nullptr;
  int gen_seen = 0;
  for (auto* it : m->items) {
    if (it->kind != ModuleItemKind::kGenerateIf) continue;
    if (gen_seen++ == 1) second = it;
  }
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(second->name, "genblk002");
}

// §27.6: "Each generate construct in a given scope is assigned a number. The
// number will be 1 for the construct that appears textually first in that
// scope and will increase by 1 for each subsequent generate construct in that
// scope." A construct carrying an explicit name takes its number all the same,
// which is what the standard's own example records when it names the construct
// written after `begin : g1` genblk4 rather than genblk3. The name reaches the
// elaborated declarations through the loop generate block's prefix
// `<enclosing><block-name>_<genvar-value>_`, so the second construct's `b` is
// named genblk2_4_b and not genblk1_4_b.
//
// The loop runs over 4 and 5 so that no index equals the storage offset of the
// variable it produces.
TEST(GenerateBlockNaming, NamedLoopConstructConsumesNumberForNextBlock) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  for (genvar i = 4; i < 6; i = i + 1) begin : first\n"
      "    logic a;\n"
      "  end\n"
      "  for (genvar j = 4; j < 6; j = j + 1) begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* mod = r.design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 4u);
  EXPECT_EQ(mod->variables[0].name, "first_4_a");
  EXPECT_EQ(mod->variables[1].name, "first_5_a");
  EXPECT_EQ(mod->variables[2].name, "genblk2_4_b");
  EXPECT_EQ(mod->variables[3].name, "genblk2_5_b");
}

// §27.6: "If such a name would conflict with an explicitly declared name, then
// leading zeros are added in front of the number until the name does not
// conflict." The parameter genblk1 is one of the explicitly declared names
// Elaborator::AssignGenerateBlockNames seeds the conflict set with, so the sole
// construct in the scope -- number 1 -- is named genblk01, and its declarations
// are elaborated under that name rather than under genblk1.
//
// The loop runs over 4 and 5 so that no index equals the storage offset of the
// variable it produces.
TEST(GenerateBlockNaming, LeadingZeroNameAppliesToBlockDeclarations) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter genblk1 = 0;\n"
      "  for (genvar i = 4; i < 6; i = i + 1) begin\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* mod = r.design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_EQ(mod->variables[0].name, "genblk01_4_x");
  EXPECT_EQ(mod->variables[1].name, "genblk01_5_x");
}

// §27.6 numbers the constructs of "a given scope", and §27.4 rules that a
// generate block "comprises a separate scope and a new level of hierarchy when
// it is instantiated", so the count starts again inside one: §27.6 writes the
// first nested construct of a block named g1 as top.g1[0].genblk1. The inner
// construct here is therefore genblk1 and not genblk2, even though the outer
// construct took number 1 in the module's scope. Each instance of the outer
// block contributes its own index to the prefix, so the inner block's `y` is
// named <outer>_<outer index>_genblk1_<inner index>_y.
//
// Both loops run over 4 and 5 so that no index equals the storage offset of the
// variable it produces.
TEST(GenerateBlockNaming, NestedConstructNumberingRestartsInBlockScope) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  for (genvar i = 4; i < 6; i = i + 1) begin : outer\n"
      "    for (genvar j = 4; j < 6; j = j + 1) begin\n"
      "      logic y;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* mod = r.design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 4u);
  EXPECT_EQ(mod->variables[0].name, "outer_4_genblk1_4_y");
  EXPECT_EQ(mod->variables[1].name, "outer_4_genblk1_5_y");
  EXPECT_EQ(mod->variables[2].name, "outer_5_genblk1_4_y");
  EXPECT_EQ(mod->variables[3].name, "outer_5_genblk1_5_y");
}

// §27.6 names the one unnamed generate block below genblk1, and that is the
// only way a genblk<n> name comes to exist, so `genblk2` names nothing and
// §23.8 reports a first name no declaration gives. The test fails on an
// elaborator that admits every name of the genblk<n> form as a first name.
TEST(GenerateBlockNaming, GenblkNameNoConstructIsGivenIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  if (1) begin\n"
      "    int a;\n"
      "  end\n"
      "  initial $display(\"%0d\", genblk2.a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'genblk2' resolves to no "
                            "declaration",
                            5, "23.8"));
}

// The name §27.6 does give, genblk1, is a declaration a first name resolves
// to, so §23.8 reports nothing of it. The test fails on a fix that drops the
// genblk<n> admission without collecting the names §27.6 assigns.
TEST(GenerateBlockNaming, GenblkNameAConstructIsGivenIsAFirstName) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  if (1) begin\n"
      "    int a;\n"
      "  end\n"
      "  initial $display(\"%0d\", genblk1.a);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "hierarchical name 'genblk1' resolves to no "
                             "declaration",
                             5, "23.8"));
}

// The genblk<n> name of a block in a module the elaborator has not reached
// when the first module is checked is collected as well. `top` is elaborated
// before `other`, which it does not instantiate.
TEST(GenerateBlockNaming, GenblkNameOfAnotherModuleIsAFirstName) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  initial $display(\"%0d\", genblk3.a);\n"
      "endmodule\n"
      "module other;\n"
      "  int x;\n"
      "  if (1) begin end\n"
      "  if (1) begin end\n"
      "  if (1) begin\n"
      "    int a;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "hierarchical name 'genblk3' resolves to no "
                             "declaration",
                             2, "23.8"));
}

// §27.4 makes a loop's unnamed block reachable by no user-chosen name, and
// `g` is declared nowhere, so §23.8 reports the first name.
TEST(GenerateBlockNaming, UserNameOnAnUnnamedLoopBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    int a;\n"
      "  end\n"
      "  initial $display(\"%0d\", g[0].a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'g' resolves to no declaration",
                            6, "23.8"));
}

}  // namespace
