#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_design.h"

using namespace delta;

namespace {

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
  EXPECT_EQ(r.cu->configs[0]->local_params[0].name, "WIDTH");
  EXPECT_EQ(r.cu->configs[0]->local_params[1].name, "DEPTH");
}

TEST(ConfigSourceText, ConfigDeclarationRequiresEndconfig) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endconfig', got EOF", 2, "33.4.1"));
}

TEST(ConfigSourceText, ConfigDeclarationRequiresDesign) {
  auto r = Parse(
      "config cfg;\n"
      "  default liblist work;\n"
      "endconfig\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "config 'cfg' is missing a 'design' statement", 1, "33.4.1.1"));
}

TEST(ConfigSourceText, ConfigDeclarationRejectsSecondDesign) {
  auto r = Parse(
      "config cfg;\n"
      "  design lib.top;\n"
      "  design lib.other;\n"
      "endconfig\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "duplicate 'design' statement in config 'cfg'", 3, "33.4.1.1"));
}

TEST(ConfigSourceText, DesignStatementQualifiedCell) {
  auto r = Parse(
      "config cfg;\n"
      "  design lib1.top;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->design_cells[0].library, "lib1");
  EXPECT_EQ(r.cu->configs[0]->design_cells[0].cell, "top");
}

TEST(ConfigSourceText, DesignStatementUnqualifiedCell) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs[0]->design_cells.size(), 1u);
  EXPECT_TRUE(r.cu->configs[0]->design_cells[0].library.empty());
  EXPECT_EQ(r.cu->configs[0]->design_cells[0].cell, "top");
}

TEST(ConfigSourceText, DesignStatementMultipleCells) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top lib2.sub cellonly;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& cells = r.cu->configs[0]->design_cells;
  ASSERT_EQ(cells.size(), 3u);
  EXPECT_EQ(cells[0].library, "work");
  EXPECT_EQ(cells[0].cell, "top");
  EXPECT_EQ(cells[1].library, "lib2");
  EXPECT_EQ(cells[1].cell, "sub");
  EXPECT_TRUE(cells[2].library.empty());
  EXPECT_EQ(cells[2].cell, "cellonly");
}

TEST(ConfigSourceText, DesignStatementEmpty) {
  auto r = Parse(
      "config cfg;\n"
      "  design ;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->configs[0]->design_cells.size(), 0u);
}

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
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  default liblist work\n"
      "endconfig\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endconfig'", 4, "33.4.1"));
}

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

TEST(ConfigSourceText, UseClauseCellWithNamedParams) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.u1 use work.alt .W(16), .D(4);\n"
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

TEST(ConfigSourceText, UseClauseParamsWithConfigSuffix) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  cell adder use work.fast_add .W(32) : config;\n"
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

TEST(ConfigSourceText, UseClauseNamingNothingIsRejected) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.u1 use;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "use clause names a cell, a parameter assignment, or both", 3,
      "A.1.5"));
}

TEST(ConfigSourceText, UseClauseConfigSuffixAloneIsRejected) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.u1 use : config;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "use clause names a cell, a parameter assignment, or both", 3,
      "A.1.5"));
}

TEST(ConfigSourceText, CellClauseUseNamingNothingIsRejected) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  cell adder use;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "use clause names a cell, a parameter assignment, or both", 3,
      "A.1.5"));
}

TEST(ConfigSourceText, UseClauseParamsAloneIsKept) {
  auto r = Parse(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.u1 use .W(8);\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_TRUE(rule->use_cell.empty());
  ASSERT_EQ(rule->use_params.size(), 1u);
}

TEST(ConfigSourceText, UseClauseCommaBeforeTheFirstAssignmentIsReported) {
  auto r = Parse(
      "config cfg;\n"
      "  design lib.top;\n"
      "  instance top.a1 use lib.adder , .W(4);\n"
      "endconfig\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a use clause's first parameter assignment follows "
                            "its cell with no comma",
                            3, "A.1.5"));
}

}  // namespace
