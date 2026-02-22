// Tests for §36-§41 System API functions (VPI, Assertion, Coverage, Data Read)

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ApiParseTest : ::testing::Test {
protected:
  CompilationUnit *Parse(const std::string &src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

// =============================================================================
// §39 Assertion control system functions
// =============================================================================

TEST_F(ApiParseTest, AssertOnSystemCall) {
  auto *unit = Parse(R"(
    module m;
      initial $assertOn;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, AssertOffSystemCall) {
  auto *unit = Parse(R"(
    module m;
      initial $assertOff;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, AssertKillSystemCall) {
  auto *unit = Parse(R"(
    module m;
      initial $assertKill;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

// =============================================================================
// §40 Coverage control system functions
// =============================================================================

TEST_F(ApiParseTest, CoverageControlSystemCall) {
  auto *unit = Parse(R"(
    module m;
      initial $coverage_control(1, 2, 3);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, CoverageGetMaxSystemCall) {
  auto *unit = Parse(R"(
    module m;
      initial begin
        int x;
        x = $coverage_get_max(0, 0);
      end
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

// =============================================================================
// §41 Data read API / General system functions
// =============================================================================

TEST_F(ApiParseTest, SdfAnnotateSystemCall) {
  auto *unit = Parse(R"(
    module m;
      initial $sdf_annotate("timing.sdf");
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, ReadmemhSystemCall) {
  auto *unit = Parse(R"(
    module m;
      logic [7:0] mem [0:255];
      initial $readmemh("data.hex", mem);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, ReadmembSystemCall) {
  auto *unit = Parse(R"(
    module m;
      logic [7:0] mem [0:255];
      initial $readmemb("data.bin", mem);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, WritememhSystemCall) {
  auto *unit = Parse(R"(
    module m;
      logic [7:0] mem [0:255];
      initial $writememh("data.hex", mem);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, MultipleApiCallsInModule) {
  auto *unit = Parse(R"(
    module m;
      initial begin
        $assertOn;
        $coverage_control(1, 0, 0);
        $readmemh("data.hex", mem);
      end
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  ASSERT_FALSE(unit->modules[0]->items.empty());
}

// =============================================================================
// §36.3 Configuration rules (config ... endconfig)
// =============================================================================

TEST_F(ApiParseTest, BasicConfigDecl) {
  auto *unit = Parse(R"(
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

TEST_F(ApiParseTest, ConfigWithDefaultLiblist) {
  auto *unit = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1 lib2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 1u);
  auto *rule = unit->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kDefault);
  ASSERT_EQ(rule->liblist.size(), 2u);
  EXPECT_EQ(rule->liblist[0], "lib1");
  EXPECT_EQ(rule->liblist[1], "lib2");
}

TEST_F(ApiParseTest, ConfigWithEndLabel) {
  auto *unit = Parse(R"(
    config my_cfg;
      design work.top;
      default liblist work;
    endconfig : my_cfg
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "my_cfg");
}

// =============================================================================
// §36.9.1 Config library (cell clause)
// =============================================================================

TEST_F(ApiParseTest, ConfigCellClauseLiblist) {
  auto *unit = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1;
      cell adder liblist lib2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto *cell_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(cell_rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(cell_rule->cell_name, "adder");
  ASSERT_EQ(cell_rule->liblist.size(), 1u);
  EXPECT_EQ(cell_rule->liblist[0], "lib2");
}

TEST_F(ApiParseTest, ConfigCellClauseWithLib) {
  auto *unit = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1;
      cell gateLib.adder use rtlLib.adder;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto *cell_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(cell_rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(cell_rule->cell_lib, "gateLib");
  EXPECT_EQ(cell_rule->cell_name, "adder");
  EXPECT_EQ(cell_rule->use_lib, "rtlLib");
  EXPECT_EQ(cell_rule->use_cell, "adder");
}

// =============================================================================
// §36.9.2 Config instance clause
// =============================================================================

TEST_F(ApiParseTest, ConfigInstanceClauseLiblist) {
  auto *unit = Parse(R"(
    config cfg1;
      design rtlLib.top;
      default liblist rtlLib;
      instance top.a2 liblist gateLib;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto *inst_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(inst_rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(inst_rule->inst_path, "top.a2");
  ASSERT_EQ(inst_rule->liblist.size(), 1u);
  EXPECT_EQ(inst_rule->liblist[0], "gateLib");
}

TEST_F(ApiParseTest, ConfigInstanceClauseUse) {
  auto *unit = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1;
      instance top.u1 use lib2.cell_impl;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto *inst_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(inst_rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(inst_rule->inst_path, "top.u1");
  EXPECT_EQ(inst_rule->use_lib, "lib2");
  EXPECT_EQ(inst_rule->use_cell, "cell_impl");
}

TEST_F(ApiParseTest, ConfigInstanceClauseUseConfig) {
  auto *unit = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1;
      instance top.bot use lib1.bot:config;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto *inst_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(inst_rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(inst_rule->use_cell, "bot");
  EXPECT_TRUE(inst_rule->use_config);
}

} // namespace
