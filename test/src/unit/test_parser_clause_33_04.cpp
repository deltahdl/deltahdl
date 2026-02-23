// §33.4: Configurations

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// =============================================================================
// A.1.5 Configuration source text
// =============================================================================
// config_declaration: config name; design statement; endconfig
TEST(SourceText, ConfigDeclBasic) {
  auto r = Parse(
      "config cfg1;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto *c = r.cu->configs[0];
  EXPECT_EQ(c->name, "cfg1");
  ASSERT_EQ(c->design_cells.size(), 1u);
  EXPECT_EQ(c->design_cells[0].first, "work");
  EXPECT_EQ(c->design_cells[0].second, "top");
  ASSERT_EQ(c->rules.size(), 1u);
  EXPECT_EQ(c->rules[0]->kind, ConfigRuleKind::kDefault);
}

// config_declaration with endconfig label
TEST(SourceText, ConfigDeclEndLabel) {
  auto r = Parse(
      "config cfg2;\n"
      "  design top;\n"
      "endconfig : cfg2\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg2");
}

// config_declaration with local_parameter_declaration
TEST(SourceText, ConfigDeclLocalParams) {
  auto r = Parse(
      "config cfg3;\n"
      "  localparam WIDTH = 8;\n"
      "  localparam DEPTH = 4;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *c = r.cu->configs[0];
  ASSERT_EQ(c->local_params.size(), 2u);
  EXPECT_EQ(c->local_params[0].first, "WIDTH");
  EXPECT_EQ(c->local_params[1].first, "DEPTH");
}

// design_statement: multiple cells, with and without library qualifier
TEST(SourceText, ConfigDesignMultipleCells) {
  auto r = Parse(
      "config cfg4;\n"
      "  design work.top lib2.sub cellonly;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *c = r.cu->configs[0];
  ASSERT_EQ(c->design_cells.size(), 3u);
  EXPECT_EQ(c->design_cells[0].first, "work");
  EXPECT_EQ(c->design_cells[0].second, "top");
  EXPECT_EQ(c->design_cells[1].first, "lib2");
  EXPECT_EQ(c->design_cells[1].second, "sub");
  // Unqualified cell: lib is empty
  EXPECT_EQ(c->design_cells[2].first, "");
  EXPECT_EQ(c->design_cells[2].second, "cellonly");
}

// config_rule_statement: default_clause liblist_clause
TEST(SourceText, ConfigRuleDefaultLiblist) {
  auto r = Parse(
      "config cfg5;\n"
      "  design top;\n"
      "  default liblist lib1 lib2 lib3;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kDefault);
  ASSERT_EQ(rule->liblist.size(), 3u);
  EXPECT_EQ(rule->liblist[0], "lib1");
  EXPECT_EQ(rule->liblist[1], "lib2");
  EXPECT_EQ(rule->liblist[2], "lib3");
}

// config_rule_statement: inst_clause liblist_clause with hierarchical inst_name
TEST(SourceText, ConfigRuleInstLiblist) {
  auto r = Parse(
      "config cfg6;\n"
      "  design top;\n"
      "  instance top.u1.u2 liblist mylib;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->inst_path, "top.u1.u2");
  ASSERT_EQ(rule->liblist.size(), 1u);
  EXPECT_EQ(rule->liblist[0], "mylib");
}

// config_rule_statement: inst_clause use_clause
TEST(SourceText, ConfigRuleInstUse) {
  auto r = Parse(
      "config cfg7;\n"
      "  design top;\n"
      "  instance top.u1 use work.alt_cell;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->inst_path, "top.u1");
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "alt_cell");
}

// config_rule_statement: cell_clause liblist_clause
TEST(SourceText, ConfigRuleCellLiblist) {
  auto r = Parse(
      "config cfg8;\n"
      "  design top;\n"
      "  cell mylib.mycell liblist lib_a lib_b;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_lib, "mylib");
  EXPECT_EQ(rule->cell_name, "mycell");
  ASSERT_EQ(rule->liblist.size(), 2u);
  EXPECT_EQ(rule->liblist[0], "lib_a");
  EXPECT_EQ(rule->liblist[1], "lib_b");
}

// config_rule_statement: cell_clause use_clause with :config suffix
TEST(SourceText, ConfigRuleCellUseConfig) {
  auto r = Parse(
      "config cfg9;\n"
      "  design top;\n"
      "  cell flip_flop use work.ff_impl :config;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_name, "flip_flop");
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "ff_impl");
  EXPECT_TRUE(rule->use_config);
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
  auto *rule = r.cu->configs[0]->rules[0];
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
  auto *rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "fast_add");
  ASSERT_EQ(rule->use_params.size(), 1u);
  EXPECT_EQ(rule->use_params[0].first, "W");
  EXPECT_TRUE(rule->use_config);
}

// Comprehensive: multiple rules of different kinds in one config
TEST(SourceText, ConfigMultipleRules) {
  auto r = Parse(
      "config cfg12;\n"
      "  design work.top;\n"
      "  default liblist work rtl;\n"
      "  instance top.dut use gate.dut_impl;\n"
      "  cell lib.ram liblist sram_lib;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *c = r.cu->configs[0];
  ASSERT_EQ(c->rules.size(), 3u);
  EXPECT_EQ(c->rules[0]->kind, ConfigRuleKind::kDefault);
  EXPECT_EQ(c->rules[1]->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(c->rules[2]->kind, ConfigRuleKind::kCell);
}

// cell_clause: unqualified cell identifier (no library prefix)
TEST(SourceText, ConfigCellUnqualified) {
  auto r = Parse(
      "config cfg13;\n"
      "  design top;\n"
      "  cell mux4 use better_mux;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_lib, "");
  EXPECT_EQ(rule->cell_name, "mux4");
  EXPECT_EQ(rule->use_cell, "better_mux");
}

}  // namespace
