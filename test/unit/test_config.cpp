// Tests for §33 Configuration declarations — detailed AST verification

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ConfigTest : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  bool HasErrors() const { return diag_.HasErrors(); }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

// =============================================================================
// §33.4.1.1 Design statement
// =============================================================================

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

// =============================================================================
// §33.4.1.2 Default clause (liblist)
// =============================================================================

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

// =============================================================================
// §33.4.1.3 Instance clause with liblist
// =============================================================================

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

// =============================================================================
// §33.4.1.4/5 Cell clause for library binding
// =============================================================================

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

// =============================================================================
// §33.4.2 Config with nested config references
// =============================================================================

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

// =============================================================================
// §33.3 Library mapping (parsing only)
// =============================================================================

TEST_F(ConfigTest, LibraryMappingConfig) {
  // Config with library-qualified design cells
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

// =============================================================================
// §33.4.3 Config with parameter override
// =============================================================================

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

// =============================================================================
// Multiple rules in single config
// =============================================================================

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

// =============================================================================
// Endconfig with label
// =============================================================================

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

}  // namespace
