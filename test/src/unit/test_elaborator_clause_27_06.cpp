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
