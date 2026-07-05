// Tests for IEEE 1800-2023 §33.4.1 "Basic configuration syntax" (Syntax 33-4).
// Each test observes the parser applying one BNF production of the config
// grammar. Semantic rules from descendant subclauses (§33.4.1.1 etc.) are not
// exercised here.
#include "fixture_parser.h"

using namespace delta;

namespace {

// config_declaration ::= config config_identifier ;
//   { local_parameter_declaration ; } design_statement
//   { config_rule_statement } endconfig [ : config_identifier ]
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
  EXPECT_EQ(cfg->local_params[0].first, "W");
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

// The { local_parameter_declaration ; } repetition admits more than one entry.
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
  EXPECT_EQ(params[0].first, "A");
  EXPECT_EQ(params[1].first, "B");
}

// config_declaration requires a ';' after the config identifier.
TEST(ConfigDeclarationParsing, MissingSemicolonAfterNameReported) {
  auto r = Parse(
      "config c\n"
      "  design top;\n"
      "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

// config_declaration requires the closing 'endconfig' keyword.
TEST(ConfigDeclarationParsing, MissingEndconfigReported) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n");
  EXPECT_TRUE(r.has_errors);
}

// design_statement ::= design { [ library_identifier . ] cell_identifier } ;
TEST(ConfigDesignStatementParsing, CollectsQualifiedAndBareCells) {
  auto r = Parse(
      "config c;\n"
      "  design work.top other;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto& cells = r.cu->configs[0]->design_cells;
  ASSERT_EQ(cells.size(), 2u);
  EXPECT_EQ(cells[0].first, "work");
  EXPECT_EQ(cells[0].second, "top");
  EXPECT_EQ(cells[1].first, "");
  EXPECT_EQ(cells[1].second, "other");
}

// design_statement ends with a required ';' terminal. Omitting it (so the
// 'endconfig' keyword appears where a cell_identifier or ';' is expected) is
// rejected rather than silently accepted.
TEST(ConfigDesignStatementParsing, MissingTerminatingSemicolonRejected) {
  auto r = Parse(
      "config c;\n"
      "  design top\n"
      "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

// design_statement's cell list is a { } repetition, so an empty list still
// forms a well-formed statement at the grammar level.
TEST(ConfigDesignStatementParsing, EmptyCellListParses) {
  auto r = Parse(
      "config c;\n"
      "  design ;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_TRUE(r.cu->configs[0]->design_cells.empty());
}

// config_rule_statement ::= default_clause liblist_clause ;
//   | inst_clause liblist_clause ; | inst_clause use_clause ;
//   | cell_clause liblist_clause ; | cell_clause use_clause ;
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

// config_rule_statement has no bare 'inst_clause ;' alternative: an inst_clause
// must be paired with a liblist_clause or a use_clause. A selection with no
// expansion clause is rejected.
TEST(ConfigRuleStatementParsing,
     InstanceSelectionWithoutExpansionClauseRejected) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a;\n"
      "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

// Likewise there is no bare 'cell_clause ;' alternative; a cell selection with
// no liblist/use expansion clause is rejected.
TEST(ConfigRuleStatementParsing, CellSelectionWithoutExpansionClauseRejected) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  cell adder;\n"
      "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

// default_clause ::= default
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

// inst_clause ::= instance inst_name
// inst_name ::= topmodule_identifier { . instance_identifier }
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

// cell_clause ::= cell [ library_identifier . ] cell_identifier
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

// liblist_clause ::= liblist { library_identifier }
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

// use_clause ::= use [ library_identifier . ] cell_identifier [ : config ]
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

// use_clause ::= use [ library_identifier . ] cell_identifier [ : config ]
// Form 1 with the optional '[ library_identifier . ]' omitted and no ': config'
// suffix: a plain unqualified cell_identifier binding.
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

// use_clause ::= use named_parameter_assignment
//   { , named_parameter_assignment } [ : config ]
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

// use_clause ::= use [ library_identifier . ] cell_identifier
//   { , named_parameter_assignment } [ : config ]
TEST(ConfigUseClauseParsing, CellFollowedByNamedParameterAssignments) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a use gateLib.adder, .W(8) : config;\n"
      "endconfig\n");
  ASSERT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_lib, "gateLib");
  EXPECT_EQ(rule->use_cell, "adder");
  ASSERT_EQ(rule->use_params.size(), 1u);
  EXPECT_EQ(rule->use_params[0].first, "W");
  EXPECT_TRUE(rule->use_config);
}

// use_clause ::= use [ library_identifier . ] cell_identifier
//   named_parameter_assignment { , named_parameter_assignment } [ : config ]
// Grammar form 3: the first named_parameter_assignment directly follows the
// cell_identifier with no separating comma.
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

// The same form is valid for a bare (unqualified) cell_identifier.
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

// The bare named_parameter_assignment form also accepts the ': config' suffix.
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

// A named_parameter_assignment value is a param_expression, so besides a
// literal it may be a reference to a parameter -- here a localparam declared by
// the config itself via a real local_parameter_declaration. This drives the
// dependency's own syntax through the parser and observes the use_clause
// capturing the (non-null) reference expression as the override value.
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
  EXPECT_EQ(cfg->local_params[0].first, "W");
  auto* rule = cfg->rules[0];
  EXPECT_EQ(rule->use_cell, "adder");
  ASSERT_EQ(rule->use_params.size(), 1u);
  EXPECT_EQ(rule->use_params[0].first, "P");
  EXPECT_NE(rule->use_params[0].second, nullptr);
}

}  // namespace
