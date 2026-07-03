#include "fixture_elaborator.h"
#include "helpers_generate_elab.h"

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
  auto* m = r.cu->modules[0];
  ModuleItem* first = nullptr;
  ModuleItem* second = nullptr;
  int gen_seen = 0;
  for (auto* it : m->items) {
    if (it->kind != ModuleItemKind::kGenerateIf) continue;
    if (gen_seen++ == 0) {
      first = it;
    } else {
      second = it;
    }
  }
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->name, "genblk1");
  EXPECT_EQ(second->name, "genblk2");
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
  auto* m = r.cu->modules[0];
  ModuleItem* first = nullptr;
  ModuleItem* second = nullptr;
  int gen_seen = 0;
  for (auto* it : m->items) {
    if (it->kind != ModuleItemKind::kGenerateIf) continue;
    if (gen_seen++ == 0) {
      first = it;
    } else {
      second = it;
    }
  }
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->name, "genblk1");

  EXPECT_EQ(second->name, "genblk02");
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

}  // namespace
