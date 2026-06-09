// Parser coverage for the BNF productions of LRM Annex A, A.1.5
// "Configuration source text". Each test observes the parser applying one of
// the grammar productions: config_declaration, design_statement,
// config_rule_statement, default_clause, inst_clause, inst_name, cell_clause,
// liblist_clause, and use_clause. The configuration parameter-override syntax
// that spells parameters with '#(...)' is defined in 33.4.3, not here, so the
// use_clause cases below exercise only the named_parameter_assignment list form
// that this subclause's grammar defines.
#include "fixture_parser.h"

using namespace delta;

namespace {

// --- config_declaration ----------------------------------------------------

// config_declaration ::= config config_identifier ; ... endconfig
TEST(ConfigSourceText, ConfigDeclarationBasic) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

// The trailing [ : config_identifier ] label is optional and, when present,
// names the declaration being closed.
TEST(ConfigSourceText, ConfigDeclarationOptionalEndLabel) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "endconfig : cfg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

// { local_parameter_declaration ; } may appear between the header and the
// design statement.
TEST(ConfigSourceText, ConfigDeclarationLocalParams) {
  auto r = Parse(
      "config cfg;\n"
      "  localparam WIDTH = 8;\n"
      "  localparam DEPTH = 4;\n"
      "  design work.top;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs[0]->local_params.size(), 2u);
  EXPECT_EQ(r.cu->configs[0]->local_params[0].first, "WIDTH");
  EXPECT_EQ(r.cu->configs[0]->local_params[1].first, "DEPTH");
}

// The endconfig terminal is required to close the declaration.
TEST(ConfigSourceText, ConfigDeclarationRequiresEndconfig) {
  EXPECT_FALSE(ParseOk(
      "config cfg;\n"
      "  design top;"));
}

// The grammar makes design_statement a mandatory member of config_declaration.
TEST(ConfigSourceText, ConfigDeclarationRequiresDesign) {
  EXPECT_FALSE(ParseOk(
      "config cfg;\n"
      "  default liblist work;\n"
      "endconfig\n"));
}

// config_declaration carries design_statement exactly once (it is not part of
// the repeated config_rule_statement group), so a second design is rejected.
TEST(ConfigSourceText, ConfigDeclarationRejectsSecondDesign) {
  EXPECT_FALSE(ParseOk(
      "config cfg;\n"
      "  design lib.top;\n"
      "  design lib.other;\n"
      "endconfig\n"));
}

// --- design_statement ------------------------------------------------------

// design_statement ::= design { [ library_identifier . ] cell_identifier } ;
TEST(ConfigSourceText, DesignStatementQualifiedCell) {
  auto r = Parse(
      "config cfg;\n"
      "  design lib1.top;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->design_cells[0].first, "lib1");
  EXPECT_EQ(r.cu->configs[0]->design_cells[0].second, "top");
}

// The library_identifier qualifier is optional on each cell.
TEST(ConfigSourceText, DesignStatementUnqualifiedCell) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs[0]->design_cells.size(), 1u);
  EXPECT_TRUE(r.cu->configs[0]->design_cells[0].first.empty());
  EXPECT_EQ(r.cu->configs[0]->design_cells[0].second, "top");
}

// The braces permit a list of cells, qualified or not, in one statement.
TEST(ConfigSourceText, DesignStatementMultipleCells) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top lib2.sub cellonly;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& cells = r.cu->configs[0]->design_cells;
  ASSERT_EQ(cells.size(), 3u);
  EXPECT_EQ(cells[0].first, "work");
  EXPECT_EQ(cells[0].second, "top");
  EXPECT_EQ(cells[1].first, "lib2");
  EXPECT_EQ(cells[1].second, "sub");
  EXPECT_TRUE(cells[2].first.empty());
  EXPECT_EQ(cells[2].second, "cellonly");
}

// The cell list may be empty (zero repetitions of the braced group).
TEST(ConfigSourceText, DesignStatementEmpty) {
  auto r = Parse(
      "config cfg;\n"
      "  design ;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->configs[0]->design_cells.size(), 0u);
}

// --- config_rule_statement -------------------------------------------------

// { config_rule_statement } -- a configuration may carry any number of rules,
// and each rule must be terminated by a semicolon.
TEST(ConfigSourceText, ConfigRuleStatementsRepeat) {
  auto r = Parse(
      "config cfg;\n"
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

TEST(ConfigSourceText, ConfigRuleRequiresSemicolon) {
  EXPECT_FALSE(ParseOk(
      "config cfg;\n"
      "  design top;\n"
      "  default liblist work\n"
      "endconfig\n"));
}

// --- default_clause and liblist_clause -------------------------------------

// config_rule_statement ::= default_clause liblist_clause ;
// default_clause ::= default ; liblist_clause ::= liblist { library_identifier }
TEST(ConfigSourceText, DefaultClauseWithLiblist) {
  auto r = Parse(
      "config cfg;\n"
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

// liblist_clause's braced library list may be empty.
TEST(ConfigSourceText, LiblistClauseEmpty) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  default liblist;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kDefault);
  EXPECT_EQ(rule->liblist.size(), 0u);
}

// --- inst_clause and inst_name ---------------------------------------------

// inst_clause ::= instance inst_name ;
// inst_name ::= topmodule_identifier { . instance_identifier } -- a single
// top-level identifier with no instance suffix is the minimal form.
TEST(ConfigSourceText, InstNameSingleIdentifier) {
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
}

// The braced instance_identifier group builds a dotted hierarchical path.
TEST(ConfigSourceText, InstNameHierarchicalPath) {
  auto r = Parse(
      "config cfg;\n"
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

// config_rule_statement ::= inst_clause use_clause ;
TEST(ConfigSourceText, InstClauseWithUseClause) {
  auto r = Parse(
      "config cfg;\n"
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

// --- cell_clause -----------------------------------------------------------

// config_rule_statement ::= cell_clause liblist_clause ;
// cell_clause ::= cell [ library_identifier . ] cell_identifier -- unqualified.
TEST(ConfigSourceText, CellClauseUnqualified) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  cell adder liblist gate_lib;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_TRUE(rule->cell_lib.empty());
  EXPECT_EQ(rule->cell_name, "adder");
}

// cell_clause with the optional library_identifier qualifier.
TEST(ConfigSourceText, CellClauseLibraryQualified) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  cell gate_lib.and2 liblist alt_lib;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_lib, "gate_lib");
  EXPECT_EQ(rule->cell_name, "and2");
}

// config_rule_statement ::= cell_clause use_clause ;
TEST(ConfigSourceText, CellClauseWithUseClause) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  cell mux4 use better_mux;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_name, "mux4");
  EXPECT_EQ(rule->use_cell, "better_mux");
}

// --- use_clause ------------------------------------------------------------

// use_clause ::= use [ library_identifier . ] cell_identifier [ : config ]
// First alternative, library-qualified cell.
TEST(ConfigSourceText, UseClauseQualifiedCell) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.u1 use lib2.cell_impl;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_lib, "lib2");
  EXPECT_EQ(rule->use_cell, "cell_impl");
  EXPECT_FALSE(rule->use_config);
}

// First alternative without the library qualifier.
TEST(ConfigSourceText, UseClauseUnqualifiedCell) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.u1 use alt_cell;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_TRUE(rule->use_lib.empty());
  EXPECT_EQ(rule->use_cell, "alt_cell");
}

// The optional [ : config ] suffix marks the bound cell as itself configured.
TEST(ConfigSourceText, UseClauseConfigSuffix) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  cell dut use work.alt_dut : config;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "alt_dut");
  EXPECT_TRUE(rule->use_config);
}

// Third alternative: a cell_identifier followed by a named_parameter_assignment
// list.
TEST(ConfigSourceText, UseClauseCellWithNamedParams) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.u1 use work.alt, .W(16), .D(4);\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "alt");
  ASSERT_EQ(rule->use_params.size(), 2u);
  EXPECT_EQ(rule->use_params[0].first, "W");
  EXPECT_EQ(rule->use_params[1].first, "D");
}

// Second alternative: a bare named_parameter_assignment list with no cell.
TEST(ConfigSourceText, UseClauseBareNamedParams) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.u1 use .WIDTH(16), .DEPTH(4);\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_TRUE(rule->use_cell.empty());
  ASSERT_EQ(rule->use_params.size(), 2u);
  EXPECT_EQ(rule->use_params[0].first, "WIDTH");
  EXPECT_EQ(rule->use_params[1].first, "DEPTH");
}

// The [ : config ] suffix may close a parameterized use_clause as well.
TEST(ConfigSourceText, UseClauseParamsWithConfigSuffix) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  cell adder use work.fast_add, .W(32) : config;\n"
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

}  // namespace
