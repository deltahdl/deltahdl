#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_design.h"

using namespace delta;

namespace {

TEST(ConfigDeclarationParsing, FullShapeWithLocalparamAndEndLabel) {
  auto r = Parse(
      "config cfg;\n"
      "  localparam W = 8;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig : cfg\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto* cfg = r.cu->configs[0];
  EXPECT_EQ(cfg->name, "cfg");
  EXPECT_EQ(cfg->local_params.size(), 1u);
  EXPECT_EQ(cfg->local_params[0].name, "W");
  EXPECT_EQ(cfg->rules.size(), 1u);
}

TEST(ConfigDeclarationParsing, MinimalConfigParses) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_TRUE(r.cu->configs[0]->local_params.empty());
}

TEST(ConfigDeclarationParsing, MultipleLocalParamsCollected) {
  auto r = Parse(
      "config c;\n"
      "  localparam A = 1;\n"
      "  localparam B = 2;\n"
      "  design top;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto& params = r.cu->configs[0]->local_params;
  ASSERT_EQ(params.size(), 2u);
  EXPECT_EQ(params[0].name, "A");
  EXPECT_EQ(params[1].name, "B");
}

TEST(ConfigDeclarationParsing, MissingSemicolonAfterNameReported) {
  auto r = Parse(
      "config c\n"
      "  design top;\n"
      "endconfig\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'design'", 2, "33.4.1"));
}

TEST(ConfigDeclarationParsing, MissingEndconfigReported) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endconfig', got EOF", 3, "33.4.1"));
}

TEST(ConfigDesignStatementParsing, CollectsQualifiedAndBareCells) {
  auto r = Parse(
      "config c;\n"
      "  design work.top other;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto& cells = r.cu->configs[0]->design_cells;
  ASSERT_EQ(cells.size(), 2u);
  EXPECT_EQ(cells[0].library, "work");
  EXPECT_EQ(cells[0].cell, "top");
  EXPECT_EQ(cells[1].library, "");
  EXPECT_EQ(cells[1].cell, "other");
}

TEST(ConfigDesignStatementParsing, MissingTerminatingSemicolonRejected) {
  auto r = Parse(
      "config c;\n"
      "  design top\n"
      "endconfig\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endconfig'", 3, "33.4.1.1"));
}

TEST(ConfigDesignStatementParsing, EmptyCellListParses) {
  auto r = Parse(
      "config c;\n"
      "  design ;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_TRUE(r.cu->configs[0]->design_cells.empty());
}

TEST(ConfigRuleStatementParsing, AllFiveAlternativesParse) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  default liblist work;\n"
      "  instance top.a liblist work;\n"
      "  instance top.b use work.alt;\n"
      "  cell rtlLib.adder liblist gateLib;\n"
      "  cell adder use gateLib.alt;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->rules.size(), 5u);
}

TEST(ConfigRuleStatementParsing,
     InstanceSelectionWithoutExpansionClauseRejected) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a;\n"
      "endconfig\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "instance selection requires a 'liblist' or 'use' clause", 3,
      "33.4.1"));
}

TEST(ConfigRuleStatementParsing, CellSelectionWithoutExpansionClauseRejected) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  cell adder;\n"
      "endconfig\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "cell selection requires a 'liblist' or 'use' clause", 3,
      "33.4.1"));
}

TEST(ConfigDefaultClauseParsing, ProducesDefaultRule) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs[0]->rules.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->rules[0]->kind, ConfigRuleKind::kDefault);
}

TEST(ConfigInstanceClauseParsing, CapturesDottedInstancePath) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a1.b liblist work;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->inst_path, "top.a1.b");
}

TEST(ConfigInstanceClauseParsing, TopModuleOnlyPath) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top liblist work;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->configs[0]->rules[0]->inst_path, "top");
}

TEST(ConfigCellClauseParsing, QualifiedAndBareForms) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  cell rtlLib.adder liblist gateLib;\n"
      "  cell adder liblist gateLib;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  auto& rules = r.cu->configs[0]->rules;
  ASSERT_EQ(rules.size(), 2u);
  EXPECT_EQ(rules[0]->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rules[0]->cell_lib, "rtlLib");
  EXPECT_EQ(rules[0]->cell_name, "adder");
  EXPECT_EQ(rules[1]->cell_lib, "");
  EXPECT_EQ(rules[1]->cell_name, "adder");
}

TEST(ConfigLiblistClauseParsing, CollectsMultipleLibraries) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  default liblist rtlLib gateLib spareLib;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  ASSERT_EQ(rule->liblist.size(), 3u);
  EXPECT_EQ(rule->liblist[0], "rtlLib");
  EXPECT_EQ(rule->liblist[1], "gateLib");
  EXPECT_EQ(rule->liblist[2], "spareLib");
}

TEST(ConfigLiblistClauseParsing, EmptyLibraryListParses) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  default liblist;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->configs[0]->rules[0]->liblist.empty());
}

TEST(ConfigUseClauseParsing, CellWithLibraryAndConfigSuffix) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a use gateLib.adder : config;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_lib, "gateLib");
  EXPECT_EQ(rule->use_cell, "adder");
  EXPECT_TRUE(rule->use_config);
}

TEST(ConfigUseClauseParsing, BareCellFormOne) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a use adder;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_lib, "");
  EXPECT_EQ(rule->use_cell, "adder");
  EXPECT_FALSE(rule->use_config);
  EXPECT_TRUE(rule->use_params.empty());
}

TEST(ConfigUseClauseParsing, BareNamedParameterAssignmentList) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a use .W(8), .D(16);\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_cell, "");
  ASSERT_EQ(rule->use_params.size(), 2u);
  EXPECT_EQ(rule->use_params[0].first, "W");
  EXPECT_EQ(rule->use_params[1].first, "D");
}

TEST(ConfigUseClauseParsing, CellFollowedByNamedParameterAssignments) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a use gateLib.adder .W(8) : config;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_lib, "gateLib");
  EXPECT_EQ(rule->use_cell, "adder");
  ASSERT_EQ(rule->use_params.size(), 1u);
  EXPECT_EQ(rule->use_params[0].first, "W");
  EXPECT_TRUE(rule->use_config);
}

TEST(ConfigUseClauseParsing, CellDirectlyFollowedByNamedParameterAssignments) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a use gateLib.adder .W(8), .D(16) : config;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_lib, "gateLib");
  EXPECT_EQ(rule->use_cell, "adder");
  ASSERT_EQ(rule->use_params.size(), 2u);
  EXPECT_EQ(rule->use_params[0].first, "W");
  EXPECT_EQ(rule->use_params[1].first, "D");
  EXPECT_TRUE(rule->use_config);
}

TEST(ConfigUseClauseParsing,
     BareCellDirectlyFollowedByNamedParameterAssignment) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a use adder .W(8);\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_lib, "");
  EXPECT_EQ(rule->use_cell, "adder");
  ASSERT_EQ(rule->use_params.size(), 1u);
  EXPECT_EQ(rule->use_params[0].first, "W");
}

TEST(ConfigUseClauseParsing, BareNamedParametersWithConfigSuffix) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a use .W(8) : config;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_cell, "");
  ASSERT_EQ(rule->use_params.size(), 1u);
  EXPECT_EQ(rule->use_params[0].first, "W");
  EXPECT_TRUE(rule->use_config);
}

TEST(ConfigUseClauseParsing, EmptyParameterExpressionAccepted) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a use .W();\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  ASSERT_EQ(rule->use_params.size(), 1u);
  EXPECT_EQ(rule->use_params[0].first, "W");
  EXPECT_EQ(rule->use_params[0].second, nullptr);
}

TEST(ConfigUseClauseParsing, ParameterOverrideValueReferencesConfigLocalparam) {
  auto r = Parse(
      "config c;\n"
      "  localparam W = 8;\n"
      "  design top;\n"
      "  instance top.a use adder .P(W);\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  auto* cfg = r.cu->configs[0];
  ASSERT_EQ(cfg->local_params.size(), 1u);
  EXPECT_EQ(cfg->local_params[0].name, "W");
  auto* rule = cfg->rules[0];
  EXPECT_EQ(rule->use_cell, "adder");
  ASSERT_EQ(rule->use_params.size(), 1u);
  EXPECT_EQ(rule->use_params[0].first, "P");
  EXPECT_NE(rule->use_params[0].second, nullptr);
}

}  // namespace
