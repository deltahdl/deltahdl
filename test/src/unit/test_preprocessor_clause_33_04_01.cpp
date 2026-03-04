#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserClause03, Cl3_10_ConfigBindingAndLibraries) {
  auto r = ParseWithPreprocessor(
      "config cfg1;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "  instance top.u1 use lib2.fast_adder;\n"
      "  cell adder liblist lib1 lib2;\n"
      "endconfig : cfg1\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg1");

  ASSERT_EQ(r.cu->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->design_cells[0].first, "work");
  EXPECT_EQ(r.cu->configs[0]->design_cells[0].second, "top");

  ASSERT_EQ(r.cu->configs[0]->rules.size(), 3u);
  EXPECT_EQ(r.cu->configs[0]->rules[0]->kind, ConfigRuleKind::kDefault);
  ASSERT_EQ(r.cu->configs[0]->rules[0]->liblist.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->rules[0]->liblist[0], "work");
  auto* r1 = r.cu->configs[0]->rules[1];
  EXPECT_EQ(r1->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(r1->inst_path, "top.u1");
  EXPECT_EQ(r1->use_lib, "lib2");
  EXPECT_EQ(r1->use_cell, "fast_adder");
  auto* r2 = r.cu->configs[0]->rules[2];
  EXPECT_EQ(r2->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(r2->cell_name, "adder");
  ASSERT_EQ(r2->liblist.size(), 2u);
}

TEST(ParserClause03, Cl3_12_1_ConfigAtCUScope) {
  auto r = ParseWithPreprocessor(
      "module lib_mod; endmodule\n"
      "config my_cfg;\n"
      "  design lib_mod;\n"
      "  default liblist;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "my_cfg");
}

}
