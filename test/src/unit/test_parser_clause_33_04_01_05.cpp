#include "fixture_config.h"
#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST_F(ConfigTest, InstanceLiblist) {
  auto* unit = Parse(R"(
    config cfg;
      design rtlLib.top;
      default liblist rtlLib;
      instance top.a2 liblist gateLib;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->rules.size(), 2u);

  auto* r0 = cfg->rules[0];
  EXPECT_EQ(r0->kind, ConfigRuleKind::kDefault);
  EXPECT_EQ(r0->liblist[0], "rtlLib");

  auto* r1 = cfg->rules[1];
  EXPECT_EQ(r1->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(r1->inst_path, "top.a2");
  ASSERT_EQ(r1->liblist.size(), 1u);
  EXPECT_EQ(r1->liblist[0], "gateLib");
}

TEST_F(ConfigTest, CellClauseLiblist) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      cell adder liblist lib2 lib3;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_EQ(unit->configs[0]->rules.size(), 1u);
  auto* rule = unit->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_TRUE(rule->cell_lib.empty());
  EXPECT_EQ(rule->cell_name, "adder");
  ASSERT_EQ(rule->liblist.size(), 2u);
  EXPECT_EQ(rule->liblist[0], "lib2");
  EXPECT_EQ(rule->liblist[1], "lib3");
}

TEST(ParserSection34, ConfigWithDefaultLiblist) {
  auto r = Parse(R"(
    config cfg1;
      design mylib.top;
      default liblist mylib rtllib;
    endconfig
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg1");
}

TEST(ParserSection34, ConfigWithMultipleLibraries) {
  auto r = Parse(R"(
    config design_cfg;
      design lib1.chip_top;
      default liblist lib1 lib2 lib3;
      instance chip_top.cpu liblist lib2;
    endconfig
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto* cfg = r.cu->configs[0];
  EXPECT_EQ(cfg->name, "design_cfg");

  ASSERT_GE(cfg->design_cells.size(), 1u);
}

}  // namespace
