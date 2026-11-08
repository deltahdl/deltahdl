#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_scratch_dir.h"
#include "parser/ast_design.h"
#include "parser/precompiled_library.h"

using namespace delta;

namespace {

TEST(PrecompiledConfig, DesignCellsAndRulesSurviveTheCompiledForm) {
  ScratchDir tmp;
  auto path = tmp.dir / "myLib.dpl";
  ASSERT_TRUE(
      PrecompiledLibrary::Save("module a;\n"
                               "endmodule\n"
                               "module b;\n"
                               "endmodule\n"
                               "config cfg;\n"
                               "  design a b;\n"
                               "  default liblist work;\n"
                               "  cell a liblist work;\n"
                               "endconfig\n",
                               "myLib", path));

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  CompilationUnit target;
  ASSERT_TRUE(PrecompiledLibrary::Load(path, target, mgr, arena, diag));
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(target.configs.size(), 1u);

  const auto* cfg = target.configs[0];
  EXPECT_EQ(cfg->name, "cfg");
  EXPECT_EQ(cfg->library, "myLib");
  ASSERT_EQ(cfg->design_cells.size(), 2u);
  EXPECT_EQ(cfg->design_cells[0].cell, "a");
  EXPECT_EQ(cfg->design_cells[1].cell, "b");
  ASSERT_EQ(cfg->rules.size(), 2u);
  EXPECT_EQ(cfg->rules[0]->kind, ConfigRuleKind::kDefault);
  EXPECT_EQ(cfg->rules[1]->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(cfg->rules[1]->cell_name, "a");
}

TEST(PrecompiledConfig, ConfigCompiledSeparatelyIsHeldBesideTheCellsItNames) {
  ScratchDir tmp;
  auto path = tmp.dir / "design.dpl";
  ASSERT_TRUE(
      PrecompiledLibrary::Save("module top;\n"
                               "endmodule\n",
                               "rtlLib", path));
  ASSERT_TRUE(
      PrecompiledLibrary::Save("config cfg;\n"
                               "  design rtlLib.top;\n"
                               "endconfig\n",
                               "cfgLib", path));

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  CompilationUnit target;
  ASSERT_TRUE(PrecompiledLibrary::Load(path, target, mgr, arena, diag));
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(target.modules.size(), 1u);
  ASSERT_EQ(target.configs.size(), 1u);
  EXPECT_EQ(target.modules[0]->library, "rtlLib");
  EXPECT_EQ(target.configs[0]->library, "cfgLib");
  ASSERT_EQ(target.configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(target.configs[0]->design_cells[0].library, "rtlLib");
  EXPECT_EQ(target.configs[0]->design_cells[0].cell, "top");
}

TEST(PrecompiledConfig, InstanceClausesSurviveTheCompiledForm) {
  ScratchDir tmp;
  auto path = tmp.dir / "myLib.dpl";
  ASSERT_TRUE(
      PrecompiledLibrary::Save("module top;\n"
                               "endmodule\n"
                               "config cfg;\n"
                               "  design top;\n"
                               "  instance top.c use gateLib.alt;\n"
                               "  instance top.d use cfg_child:config;\n"
                               "endconfig\n",
                               "myLib", path));

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  CompilationUnit target;
  ASSERT_TRUE(PrecompiledLibrary::Load(path, target, mgr, arena, diag));
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(target.configs.size(), 1u);

  const auto* cfg = target.configs[0];
  ASSERT_EQ(cfg->rules.size(), 2u);
  EXPECT_EQ(cfg->rules[0]->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(cfg->rules[0]->inst_path, "top.c");
  EXPECT_EQ(cfg->rules[0]->use_lib, "gateLib");
  EXPECT_EQ(cfg->rules[0]->use_cell, "alt");
  EXPECT_FALSE(cfg->rules[0]->use_config);
  EXPECT_EQ(cfg->rules[1]->inst_path, "top.d");
  EXPECT_EQ(cfg->rules[1]->use_cell, "cfg_child");
  EXPECT_TRUE(cfg->rules[1]->use_config);
}

TEST(PrecompiledConfig, ConfigLocalParametersSurviveTheCompiledForm) {
  ScratchDir tmp;
  auto path = tmp.dir / "myLib.dpl";
  ASSERT_TRUE(
      PrecompiledLibrary::Save("module top;\n"
                               "endmodule\n"
                               "config cfg;\n"
                               "  localparam W = 8;\n"
                               "  design top;\n"
                               "endconfig\n",
                               "myLib", path));

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  CompilationUnit target;
  ASSERT_TRUE(PrecompiledLibrary::Load(path, target, mgr, arena, diag));
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(target.configs.size(), 1u);

  const auto* cfg = target.configs[0];
  ASSERT_EQ(cfg->local_params.size(), 1u);
  EXPECT_EQ(cfg->local_params[0].name, "W");
  EXPECT_NE(cfg->local_params[0].init_expr, nullptr);
}

}  // namespace
