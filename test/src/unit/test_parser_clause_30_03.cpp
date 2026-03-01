// §30.3: Specify block declaration

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- list_of_specparam_assignments ---
// specparam_assignment { , specparam_assignment }
TEST(ParserA23, ListOfSpecparamAssignmentsSingle) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam tRISE = 100; endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// system_timing_check is a specify_item (mixed with paths)
TEST(ParserA705, TimingCheckMixedWithPaths) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  (a => b) = 5;\n"
      "  $setup(data, posedge clk, 10);\n"
      "  (c *> d) = 10;\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 3u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(spec->specify_items[2]->kind, SpecifyItemKind::kPathDecl);
}

TEST(ParserAnnexA, A7SpecparamInSpecify) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tRISE = 100;\n"
      "    (a => b) = tRISE;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

ModuleItem* FindSpecifyBlock(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
  }
  return nullptr;
}

// =============================================================================
// A.7.1 specify_block ::= specify { specify_item } endspecify
// =============================================================================
TEST(ParserA701, SpecifyBlockEmpty) {
  auto r = Parse("module m; specify endspecify endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->kind, ModuleItemKind::kSpecifyBlock);
  EXPECT_EQ(spec->specify_items.size(), 0u);
}

TEST(ParserA701, SpecifyBlockMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "    (c => d) = 10;\n"
      "    $setup(data, posedge clk, 3);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 3u);
}

// =============================================================================
// A.7.1 specify_item — all 5 alternatives
// =============================================================================
TEST(ParserA701, SpecifyItemSpecparamDecl) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tPD = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kSpecparam);
}

TEST(ParserA701, SpecifyItemAllFiveKinds) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tPD = 5;\n"
      "    pulsestyle_onevent out1;\n"
      "    showcancelled out2;\n"
      "    (a => b) = tPD;\n"
      "    $setup(data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 5u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kSpecparam);
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_EQ(spec->specify_items[2]->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_EQ(spec->specify_items[3]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[4]->kind, SpecifyItemKind::kTimingCheck);
}

// =============================================================================
// A.7.1 specify_block coexistence with other module items
// =============================================================================
TEST(ParserA701, SpecifyBlockCoexistsWithModuleItems) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "  assign a = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kSpecifyBlock);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kContAssign);
}

using ConfigParseTest = ProgramTestParse;

TEST(ParserSection28, Sec28_12_MixedPathsAndTimingChecks) {
  EXPECT_TRUE(
      ParseOk("module m(input a, d, clk, output b);\n"
              "  specify\n"
              "    specparam tPD = 10;\n"
              "    (a => b) = tPD;\n"
              "    $setup(d, posedge clk, 5);\n"
              "    $hold(posedge clk, d, 3);\n"
              "    showcancelled b;\n"
              "    pulsestyle_onevent b;\n"
              "  endspecify\n"
              "endmodule\n"));
}

}  // namespace
