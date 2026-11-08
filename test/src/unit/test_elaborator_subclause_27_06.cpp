#include <gtest/gtest.h>

#include <string>

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

TEST(GenerateBlockNaming, GenblkNameAConstructIsGivenIsReportedAsUnnamed) {
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name reaches into unnamed generate "
                            "block 'genblk1'",
                            5, "27.6"));
}

TEST(GenerateBlockNaming, ReachingIntoAnUnnamedBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  if (1) begin\n"
      "    int a;\n"
      "  end\n"
      "  for (genvar i = 0; i < 2; i++) begin\n"
      "    int b;\n"
      "  end\n"
      "  initial $display(\"%0d %0d\", genblk1.a, genblk2[0].b);\n"
      "  initial $display(\"%0d\", top.genblk1.a);\n"
      "endmodule\n",
      f);
  const char* conditional_report =
      "hierarchical name reaches into unnamed generate block 'genblk1'";
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), conditional_report, 8, "27.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name reaches into unnamed generate "
                            "block 'genblk2'",
                            8, "27.6"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), conditional_report, 9, "27.6"));
}

TEST(GenerateBlockNaming, EveryUnnamedBlockOfAConstructIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(parameter P = 0) ();\n"
      "  if (P) begin : named int a; end else begin int b; end\n"
      "  case (P) 0: begin int c; end default: begin : d int e; end endcase\n"
      "  if (1) if (P) begin int g; end\n"
      "  for (genvar i = 0; i < 2; i++) begin : loop int h; end\n"
      "  initial $display(\"%0d %0d %0d\", genblk1.b, genblk2.c, genblk3.g);\n"
      "  initial $display(\"%0d %0d %0d\", named.a, d.e, loop[1].h);\n"
      "endmodule\n",
      f);
  for (const char* block : {"genblk1", "genblk2", "genblk3"}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::string("hierarchical name reaches into unnamed generate block '") +
            block + "'",
        6, "27.6"))
        << block;
  }
  for (const auto& diag : f.diag.Diagnostics()) {
    EXPECT_NE(diag.loc.line, 7u) << diag.message;
  }
}

TEST(GenerateBlockNaming, GenblkNameOfAnotherModuleIsReported) {
  ElabFixture f;
  ElaborateWithPreprocessor(
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
      f, "", true);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'genblk3' resolves to no "
                            "declaration",
                            2, "23.8"));
}

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
