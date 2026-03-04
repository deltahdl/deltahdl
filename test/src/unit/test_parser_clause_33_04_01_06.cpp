// §33.4.1.6: The use clause

#include "fixture_config.h"
#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// config_rule_statement: inst_clause use_clause
TEST(SourceText, ConfigRuleInstUse) {
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

// use_clause: use with named_parameter_assignment
TEST(SourceText, ConfigUseNamedParams) {
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

// use_clause: use [lib.] cell named_parameter_assignment (combined form)
TEST(SourceText, ConfigUseCellAndParams) {
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

// =============================================================================
// §33.4.1.3/6 Instance clause with use binding
// =============================================================================
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

TEST(ParserSection34, ConfigWithUseClause) {
  // Config with use clause to specify library cell binding
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

}  // namespace
