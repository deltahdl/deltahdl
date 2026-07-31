#include <gtest/gtest.h>

#include <filesystem>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_scratch_dir.h"
#include "parser/ast.h"
#include "parser/precompiled_library.h"

using namespace delta;

namespace {

// §33.5.4: where a separate compilation tool did the compiling, the tool that
// binds afterwards can be given the configuration to use instead of the names
// of the top-level cells -- and in that strategy the configuration is itself
// precompiled. So the compiled form has to carry everything a bind reads out of
// a configuration, because the bind will never see the source description it
// was written from: the cells its design statement names, and the rules that
// bind the instances below them.

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
  EXPECT_EQ(cfg->design_cells[0].second, "a");
  EXPECT_EQ(cfg->design_cells[1].second, "b");
  ASSERT_EQ(cfg->rules.size(), 2u);
  EXPECT_EQ(cfg->rules[0]->kind, ConfigRuleKind::kDefault);
  EXPECT_EQ(cfg->rules[1]->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(cfg->rules[1]->cell_name, "a");
}

// The configuration need not have been compiled by the same invocation that
// compiled the cells it configures, nor into the same library: it is a design
// element like any other, so a compile of its own puts it in the filesystem
// beside them, and one read gathers the configuration and the cells together.
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
  EXPECT_EQ(target.configs[0]->design_cells[0].first, "rtlLib");
  EXPECT_EQ(target.configs[0]->design_cells[0].second, "top");
}

// The rule shape the round-trip above leaves out. An instance clause carries
// more than a kind and a name -- the instance path it selects, the library and
// cell its use clause expands to, and whether that use clause reaches a
// configuration rather than a cell -- and a bind driven by the compiled form
// reads every one of those out of it.
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

// A configuration may declare constants of its own ahead of its design
// statement, and the parameter overrides its rules carry are written in terms
// of them. They are part of the configuration, so they travel with it into the
// compiled form rather than being resolved away when it is written.
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
  EXPECT_EQ(cfg->local_params[0].first, "W");
  EXPECT_NE(cfg->local_params[0].second, nullptr);
}

}  // namespace
