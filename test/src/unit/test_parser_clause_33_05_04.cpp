#include <gtest/gtest.h>
#include <unistd.h>

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "parser/precompiled_library.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

struct TempPrecompDir {
  fs::path dir;
  TempPrecompDir() {
    static std::atomic<uint64_t> counter{0};
    auto seq = counter.fetch_add(1);
    dir = fs::temp_directory_path() /
          ("delta_clause_33_05_04_parser_" + std::to_string(::getpid()) + "_" +
           std::to_string(seq));
    fs::create_directories(dir);
  }
  ~TempPrecompDir() {
    std::error_code ec;
    fs::remove_all(dir, ec);
  }
};

// §33.5.4: in the separate-compilation strategy the config itself shall also be
// precompiled. The precompiled library persists configs alongside cells, so a
// saved config — its name, owning library, design cells, and binding rules —
// survives the save/load round trip intact.
TEST(ConfigCommandLine, ConfigDesignCellsAndRulesRoundTrip) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "lib.dpl";
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

}  // namespace
