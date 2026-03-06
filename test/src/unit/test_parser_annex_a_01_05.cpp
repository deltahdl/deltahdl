#include "fixture_parser.h"

using namespace delta;

namespace {

// §A.1.5 Configuration source text

// config_declaration ::= config id ; { localparam ; } design_stmt
//                        { config_rule_statement } endconfig [ : id ]

TEST(ConfigA15, BasicConfig) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

TEST(ConfigA15, ConfigWithEndLabel) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "endconfig : cfg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// design_statement ::= design { [lib.] cell } ;
TEST(ConfigA15, DesignMultipleCells) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top lib2.sub;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->configs[0]->design_cells.size(), 2u);
}

// default_clause liblist_clause
TEST(ConfigA15, DefaultLiblist) {
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

// inst_clause liblist_clause
TEST(ConfigA15, InstLiblist) {
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

// inst_clause use_clause
TEST(ConfigA15, InstUseClause) {
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

// cell_clause liblist_clause
TEST(ConfigA15, CellLiblist) {
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

// cell_clause with library-qualified cell: cell [lib.] cell_id
TEST(ConfigA15, CellLibQualified) {
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

// use_clause with :config suffix
TEST(ConfigA15, UseClauseConfig) {
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

// use_clause with named parameter assignments
TEST(ConfigA15, UseClauseWithParams) {
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

// config with localparam
TEST(ConfigA15, ConfigWithLocalparam) {
  auto r = Parse(
      "config cfg;\n"
      "  localparam W = 8;\n"
      "  design work.top;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->configs[0]->local_params.size(), 1u);
}

// Multiple config rules
TEST(ConfigA15, MultipleRules) {
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

}  // namespace
