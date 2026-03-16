#include "fixture_config.h"
#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

TEST(ConfigParsing, BasicConfig) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

TEST(ConfigParsing, ConfigWithEndLabel) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "endconfig : cfg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConfigParsing, DesignMultipleCells) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top lib2.sub;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->configs[0]->design_cells.size(), 2u);
}

TEST(ConfigParsing, DefaultLiblist) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "  default liblist work rtl;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs[0]->rules.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->rules[0]->kind, ConfigRuleKind::kDefault);
  EXPECT_EQ(r.cu->configs[0]->rules[0]->liblist.size(), 2u);
}

TEST(ConfigParsing, InstLiblist) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "  instance top.u1 liblist rtl;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs[0]->rules.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->rules[0]->kind, ConfigRuleKind::kInstance);
}

TEST(ConfigParsing, InstUseClause) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "  instance top.u1 use work.alt_cell;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "alt_cell");
}

TEST(ConfigParsing, CellLiblist) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "  cell adder liblist gate_lib;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_name, "adder");
}

TEST(ConfigParsing, CellLibQualified) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "  cell gate_lib.and2 liblist alt_lib;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->cell_lib, "gate_lib");
  EXPECT_EQ(rule->cell_name, "and2");
}

TEST(ConfigParsing, UseClauseConfig) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "  cell dut use work.alt_dut :config;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_TRUE(rule->use_config);
}

TEST(ConfigParsing, UseClauseWithParams) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "  instance top.u1 use work.alt #(.W(16), .D(4));\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_params.size(), 2u);
}

TEST(ConfigParsing, ConfigWithLocalparam) {
  auto r = Parse(
      "config cfg;\n"
      "  localparam W = 8;\n"
      "  design work.top;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->configs[0]->local_params.size(), 1u);
}

TEST(ConfigParsing, MultipleRules) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "  instance top.u1 use work.alt;\n"
      "  cell mux2 liblist gate_lib;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->configs[0]->rules.size(), 3u);
}

TEST(ConfigParsing, BasicDeclaration) {
  auto r = Parse(
      "config cfg1;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto* c = r.cu->configs[0];
  EXPECT_EQ(c->name, "cfg1");
  ASSERT_EQ(c->design_cells.size(), 1u);
  EXPECT_EQ(c->design_cells[0].first, "work");
  EXPECT_EQ(c->design_cells[0].second, "top");
  ASSERT_EQ(c->rules.size(), 1u);
  EXPECT_EQ(c->rules[0]->kind, ConfigRuleKind::kDefault);
}

TEST(ConfigParsing, MultipleLocalparams) {
  auto r = Parse(
      "config cfg3;\n"
      "  localparam WIDTH = 8;\n"
      "  localparam DEPTH = 4;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* c = r.cu->configs[0];
  ASSERT_EQ(c->local_params.size(), 2u);
  EXPECT_EQ(c->local_params[0].first, "WIDTH");
  EXPECT_EQ(c->local_params[1].first, "DEPTH");
}

TEST(ConfigParsing, DefaultLiblistThreeEntries) {
  auto r = Parse(
      "config cfg5;\n"
      "  design top;\n"
      "  default liblist lib1 lib2 lib3;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kDefault);
  ASSERT_EQ(rule->liblist.size(), 3u);
  EXPECT_EQ(rule->liblist[0], "lib1");
  EXPECT_EQ(rule->liblist[1], "lib2");
  EXPECT_EQ(rule->liblist[2], "lib3");
}

TEST(ConfigParsing, QualifiedCellLiblist) {
  auto r = Parse(
      "config cfg8;\n"
      "  design top;\n"
      "  cell mylib.mycell liblist lib_a lib_b;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_lib, "mylib");
  EXPECT_EQ(rule->cell_name, "mycell");
  ASSERT_EQ(rule->liblist.size(), 2u);
  EXPECT_EQ(rule->liblist[0], "lib_a");
  EXPECT_EQ(rule->liblist[1], "lib_b");
}

TEST_F(ApiParseTest, BasicConfigDeclaration) {
  auto* unit = Parse(R"(
    config cfg1;
      design rtlLib.top;
      default liblist rtlLib;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg1");
  ASSERT_EQ(unit->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(unit->configs[0]->design_cells[0].first, "rtlLib");
  EXPECT_EQ(unit->configs[0]->design_cells[0].second, "top");
}

TEST(ConfigParsing, CellUseConfigFlag) {
  auto r = Parse(
      "config cfg9;\n"
      "  design top;\n"
      "  cell flip_flop use work.ff_impl :config;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_name, "flip_flop");
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "ff_impl");
  EXPECT_TRUE(rule->use_config);
}

TEST(ConfigParsing, ThreeDistinctRuleKinds) {
  auto r = Parse(
      "config cfg12;\n"
      "  design work.top;\n"
      "  default liblist work rtl;\n"
      "  instance top.dut use gate.dut_impl;\n"
      "  cell lib.ram liblist sram_lib;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* c = r.cu->configs[0];
  ASSERT_EQ(c->rules.size(), 3u);
  EXPECT_EQ(c->rules[0]->kind, ConfigRuleKind::kDefault);
  EXPECT_EQ(c->rules[1]->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(c->rules[2]->kind, ConfigRuleKind::kCell);
}

TEST(ConfigParsing, EndLabelMatchesName) {
  auto r = Parse(
      "config cfg2;\n"
      "  design top;\n"
      "endconfig : cfg2\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg2");
}

TEST_F(ConfigTest, LibraryMappingConfig) {
  auto* unit = Parse(R"(
    config cfg;
      design rtlLib.top;
      default liblist rtlLib;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->design_cells.size(), 1u);
  EXPECT_EQ(cfg->design_cells[0].first, "rtlLib");
  EXPECT_EQ(cfg->design_cells[0].second, "top");
  ASSERT_EQ(cfg->rules.size(), 1u);
  EXPECT_EQ(cfg->rules[0]->liblist[0], "rtlLib");
}

TEST_F(ConfigTest, MultipleRulesInConfig) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      default liblist rtlLib;
      instance top.a1 use lib.fast_adder;
      cell mux use lib.fast_mux;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->rules.size(), 3u);
  EXPECT_EQ(cfg->rules[0]->kind, ConfigRuleKind::kDefault);
  EXPECT_EQ(cfg->rules[1]->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(cfg->rules[2]->kind, ConfigRuleKind::kCell);
}

TEST_F(ConfigTest, EndconfigWithLabel) {
  auto* unit = Parse(R"(
    config my_config;
      design lib.top;
    endconfig : my_config
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "my_config");
  EXPECT_FALSE(HasErrors());
}

TEST_F(ConfigParseTest, BasicConfig) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST_F(ConfigParseTest, ConfigWithEndLabel) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
    endconfig : cfg
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST(ConfigDeclaration, EndLabelAfterModule) {
  auto r = Parse(
      "module m; endmodule\n"
      "config cfg;\n"
      "  design m;\n"
      "endconfig : cfg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

TEST(ConfigDeclaration, MissingEndconfigIsError) {
  EXPECT_FALSE(ParseOk(
      "module m; endmodule\n"
      "config c;\n"
      "  design m;"));
}

TEST(ConfigParsing, KeywordStartsDeclaration) {
  auto r = Parse(
      "module m; endmodule\n"
      "config cfg; design m; endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

TEST(ConfigParsing, DesignMixedQualification) {
  auto r = Parse(
      "config cfg4;\n"
      "  design work.top lib2.sub cellonly;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* c = r.cu->configs[0];
  ASSERT_EQ(c->design_cells.size(), 3u);
  EXPECT_EQ(c->design_cells[0].first, "work");
  EXPECT_EQ(c->design_cells[0].second, "top");
  EXPECT_EQ(c->design_cells[1].first, "lib2");
  EXPECT_EQ(c->design_cells[1].second, "sub");

  EXPECT_EQ(c->design_cells[2].first, "");
  EXPECT_EQ(c->design_cells[2].second, "cellonly");
}

TEST_F(ConfigTest, DesignStatementParsed) {
  auto* unit = Parse(R"(
    config cfg;
      design lib1.top;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  EXPECT_EQ(cfg->name, "cfg");
  ASSERT_EQ(cfg->design_cells.size(), 1u);
  EXPECT_EQ(cfg->design_cells[0].first, "lib1");
  EXPECT_EQ(cfg->design_cells[0].second, "top");
}

TEST_F(ConfigTest, DesignStatementNoLib) {
  auto* unit = Parse(R"(
    config cfg;
      design top;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->design_cells.size(), 1u);
  EXPECT_TRUE(cfg->design_cells[0].first.empty());
  EXPECT_EQ(cfg->design_cells[0].second, "top");
}

TEST_F(ConfigTest, DesignStatementMultipleTopCells) {
  auto* unit = Parse(R"(
    config cfg;
      design lib1.top1 lib2.top2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->design_cells.size(), 2u);
  EXPECT_EQ(cfg->design_cells[0].first, "lib1");
  EXPECT_EQ(cfg->design_cells[0].second, "top1");
  EXPECT_EQ(cfg->design_cells[1].first, "lib2");
  EXPECT_EQ(cfg->design_cells[1].second, "top2");
}

TEST_F(ConfigTest, DefaultLiblist) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      default liblist lib1 lib2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->rules.size(), 1u);
  auto* rule = cfg->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kDefault);
  ASSERT_EQ(rule->liblist.size(), 2u);
  EXPECT_EQ(rule->liblist[0], "lib1");
  EXPECT_EQ(rule->liblist[1], "lib2");
}

TEST_F(ConfigTest, DefaultLiblistSingleLib) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      default liblist mylib;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_EQ(unit->configs[0]->rules.size(), 1u);
  auto* rule = unit->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kDefault);
  ASSERT_EQ(rule->liblist.size(), 1u);
  EXPECT_EQ(rule->liblist[0], "mylib");
}

TEST(ConfigParsing, CoexistsWithModule) {
  auto r = Parse(R"(
    module protected_ip;
      logic [7:0] data;
    endmodule

    config ip_cfg;
      design work.protected_ip;
      default liblist work;
    endconfig
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "protected_ip");
  EXPECT_EQ(r.cu->configs[0]->name, "ip_cfg");
}

TEST_F(ConfigParseTest, ConfigWithDefaultClause) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      default liblist lib1 lib2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST(ConfigParsing, HierarchicalInstLiblist) {
  auto r = Parse(
      "config cfg6;\n"
      "  design top;\n"
      "  instance top.u1.u2 liblist mylib;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->inst_path, "top.u1.u2");
  ASSERT_EQ(rule->liblist.size(), 1u);
  EXPECT_EQ(rule->liblist[0], "mylib");
}

TEST_F(ApiParseTest, ConfigInstanceClauseLiblist) {
  auto* unit = Parse(R"(
    config cfg1;
      design rtlLib.top;
      default liblist rtlLib;
      instance top.a2 liblist gateLib;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto* inst_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(inst_rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(inst_rule->inst_path, "top.a2");
  ASSERT_EQ(inst_rule->liblist.size(), 1u);
  EXPECT_EQ(inst_rule->liblist[0], "gateLib");
}

TEST(ConfigParsing, TwoInstanceRules) {
  auto r = Parse(R"(
    config inst_cfg;
      design work.top;
      instance top.u1 liblist gatelib;
      instance top.u2 liblist rtllib;
    endconfig
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto* cfg = r.cu->configs[0];
  ASSERT_GE(cfg->rules.size(), 2u);
}

TEST_F(ConfigParseTest, ConfigWithInstanceClause) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      instance top.u1 liblist lib2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST_F(ApiParseTest, ConfigCellClauseLiblist) {
  auto* unit = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1;
      cell adder liblist lib2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto* cell_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(cell_rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(cell_rule->cell_name, "adder");
  ASSERT_EQ(cell_rule->liblist.size(), 1u);
  EXPECT_EQ(cell_rule->liblist[0], "lib2");
}

TEST_F(ApiParseTest, ConfigCellClauseWithLib) {
  auto* unit = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1;
      cell gateLib.adder use rtlLib.adder;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto* cell_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(cell_rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(cell_rule->cell_lib, "gateLib");
  EXPECT_EQ(cell_rule->cell_name, "adder");
  EXPECT_EQ(cell_rule->use_lib, "rtlLib");
  EXPECT_EQ(cell_rule->use_cell, "adder");
}

TEST(ConfigParsing, UnqualifiedCellUse) {
  auto r = Parse(
      "config cfg13;\n"
      "  design top;\n"
      "  cell mux4 use better_mux;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_lib, "");
  EXPECT_EQ(rule->cell_name, "mux4");
  EXPECT_EQ(rule->use_cell, "better_mux");
}

TEST_F(ConfigParseTest, ConfigWithCellClause) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      cell top use lib.other;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

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

TEST(ConfigParsing, DefaultLiblistVerifiesName) {
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

TEST(ConfigParsing, DefaultAndInstanceRules) {
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

TEST(ConfigParsing, InstUseRule) {
  auto r = Parse(
      "config cfg7;\n"
      "  design top;\n"
      "  instance top.u1 use work.alt_cell;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->inst_path, "top.u1");
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "alt_cell");
}

TEST(ConfigParsing, UseNamedParams) {
  auto r = Parse(
      "config cfg10;\n"
      "  design top;\n"
      "  instance top.u1 use #(.WIDTH(16), .DEPTH(4));\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  ASSERT_EQ(rule->use_params.size(), 2u);
  EXPECT_EQ(rule->use_params[0].first, "WIDTH");
  EXPECT_EQ(rule->use_params[1].first, "DEPTH");
}

TEST(ConfigParsing, UseCellParamsAndConfig) {
  auto r = Parse(
      "config cfg11;\n"
      "  design top;\n"
      "  cell adder use work.fast_add #(.W(32)) :config;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "fast_add");
  ASSERT_EQ(rule->use_params.size(), 1u);
  EXPECT_EQ(rule->use_params[0].first, "W");
  EXPECT_TRUE(rule->use_config);
}

TEST_F(ApiParseTest, ConfigInstanceClauseUse) {
  auto* unit = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1;
      instance top.u1 use lib2.cell_impl;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto* inst_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(inst_rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(inst_rule->inst_path, "top.u1");
  EXPECT_EQ(inst_rule->use_lib, "lib2");
  EXPECT_EQ(inst_rule->use_cell, "cell_impl");
}

TEST_F(ApiParseTest, ConfigInstanceClauseUseConfig) {
  auto* unit = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1;
      instance top.bot use lib1.bot:config;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto* inst_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(inst_rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(inst_rule->use_cell, "bot");
  EXPECT_TRUE(inst_rule->use_config);
}

TEST_F(ConfigTest, InstanceUseClause) {
  auto* unit = Parse(R"(
    config cfg;
      design lib1.top;
      instance top.u1 use lib2.adder;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_EQ(unit->configs[0]->rules.size(), 1u);
  auto* rule = unit->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->inst_path, "top.u1");
  EXPECT_EQ(rule->use_lib, "lib2");
  EXPECT_EQ(rule->use_cell, "adder");
  EXPECT_FALSE(rule->use_config);
}

TEST_F(ConfigTest, CellClauseWithLibUse) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      cell mylib.adder use otherlib.fast_adder;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_EQ(unit->configs[0]->rules.size(), 1u);
  auto* rule = unit->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_lib, "mylib");
  EXPECT_EQ(rule->cell_name, "adder");
  EXPECT_EQ(rule->use_lib, "otherlib");
  EXPECT_EQ(rule->use_cell, "fast_adder");
}

TEST(ConfigParsing, CellUseVerifiesName) {
  auto r = Parse(R"(
    config map_cfg;
      design work.top;
      cell ram_cell use gatelib.ram_gate;
    endconfig
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "map_cfg");
  ASSERT_GE(r.cu->configs[0]->rules.size(), 1u);
}

TEST_F(ConfigTest, NestedConfigReference) {
  auto* unit = Parse(R"(
    config bot;
      design lib1.bot;
      default liblist lib1 lib2;
    endconfig
    config top;
      design lib1.top;
      instance top.bot use lib1.bot :config;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 2u);
  EXPECT_EQ(unit->configs[0]->name, "bot");
  EXPECT_EQ(unit->configs[1]->name, "top");

  ASSERT_EQ(unit->configs[1]->rules.size(), 1u);
  auto* rule = unit->configs[1]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->use_lib, "lib1");
  EXPECT_EQ(rule->use_cell, "bot");
  EXPECT_TRUE(rule->use_config);
}

TEST_F(ConfigTest, UseClauseWithParams) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      instance top.u1 use lib.adder #(.WIDTH(16), .DEPTH(4));
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_EQ(unit->configs[0]->rules.size(), 1u);
  auto* rule = unit->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->use_lib, "lib");
  EXPECT_EQ(rule->use_cell, "adder");
  ASSERT_EQ(rule->use_params.size(), 2u);
  EXPECT_EQ(rule->use_params[0].first, "WIDTH");
  EXPECT_EQ(rule->use_params[1].first, "DEPTH");
}

TEST_F(ConfigTest, LocalparamInConfig) {
  auto* unit = Parse(R"(
    config cfg;
      localparam W = 32;
      design lib.top;
      default liblist lib;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->local_params.size(), 1u);
  EXPECT_EQ(cfg->local_params[0].first, "W");
  EXPECT_NE(cfg->local_params[0].second, nullptr);
}

TEST(ConfigParsing, EmptyLiblist) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  default liblist;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs[0]->rules.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->rules[0]->kind, ConfigRuleKind::kDefault);
  EXPECT_EQ(r.cu->configs[0]->rules[0]->liblist.size(), 0u);
}

TEST(ConfigParsing, ConfigWithNoRules) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->rules.size(), 0u);
}

TEST(ConfigParsing, SingleLevelInstPath) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  instance top liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->inst_path, "top");
  ASSERT_EQ(rule->liblist.size(), 1u);
}

TEST(ConfigParsing, EndLabelMismatchIsError) {
  EXPECT_FALSE(ParseOk(
      "config cfg;\n"
      "  design top;\n"
      "endconfig : wrong_name\n"));
}

TEST(ConfigParsing, MultipleConfigsInOneUnit) {
  auto r = Parse(
      "config cfg_a;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig\n"
      "config cfg_b;\n"
      "  design lib2.sub;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 2u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg_a");
  EXPECT_EQ(r.cu->configs[1]->name, "cfg_b");
}

TEST(ConfigParsing, UseParamsOnly) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.u1 use #(.W(8));\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->use_cell, "");
  ASSERT_EQ(rule->use_params.size(), 1u);
  EXPECT_EQ(rule->use_params[0].first, "W");
}

TEST(ConfigParsing, EmptyDesignStatement) {
  auto r = Parse(
      "config cfg;\n"
      "  design ;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->configs[0]->design_cells.size(), 0u);
}

TEST(ConfigParsing, InstUseUnqualifiedCell) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.u1 use alt_cell;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->use_lib, "");
  EXPECT_EQ(rule->use_cell, "alt_cell");
}

TEST(ConfigParsing, CellLiblistEmpty) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  cell mux liblist;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_name, "mux");
  EXPECT_EQ(rule->liblist.size(), 0u);
}

TEST(ConfigParsing, InstanceLiblistEmpty) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.u1 liblist;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->inst_path, "top.u1");
  EXPECT_EQ(rule->liblist.size(), 0u);
}

TEST(ConfigParsing, UseConfigFlagAlone) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.u1 use work.sub :config;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "sub");
  EXPECT_TRUE(rule->use_config);
  EXPECT_EQ(rule->use_params.size(), 0u);
}

TEST(ConfigParsing, DeeplyNestedInstPath) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.a.b.c.d liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->inst_path, "top.a.b.c.d");
}

TEST(ConfigParsing, MissingSemicolonAfterDesign) {
  EXPECT_FALSE(ParseOk(
      "config cfg;\n"
      "  design top\n"
      "endconfig\n"));
}

TEST(ConfigParsing, MissingSemicolonAfterRule) {
  EXPECT_FALSE(ParseOk(
      "config cfg;\n"
      "  design top;\n"
      "  default liblist work\n"
      "endconfig\n"));
}

TEST(ConfigParsing, MissingDesignStatementIsError) {
  EXPECT_FALSE(ParseOk(
      "config cfg;\n"
      "  default liblist work;\n"
      "endconfig\n"));
}

}  // namespace
