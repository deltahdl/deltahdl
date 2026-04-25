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
          ("delta_clause_33_05_04_parser_" + std::to_string(::getpid()) +
           "_" + std::to_string(seq));
    fs::create_directories(dir);
  }
  ~TempPrecompDir() {
    std::error_code ec;
    fs::remove_all(dir, ec);
  }
};

// §33.5.4: in the separate-compilation-tool strategy "the config
// itself shall also be precompiled."  A round-trip through the
// precompiled-library archive must restore every part of the config
// the binding tool will later consult — its name, its library tag,
// and the cells named in its design statement — not just the fact
// that a config existed.
TEST(ConfigCommandLine, ConfigPersistsThroughPrecompiledLibrary) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "lib.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(
      "module top;\n"
      "endmodule\n"
      "config cfg;\n"
      "  design top;\n"
      "endconfig\n",
      "rtlLib", path));

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  CompilationUnit target;
  ASSERT_TRUE(PrecompiledLibrary::Load(path, target, mgr, arena, diag));
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(target.configs.size(), 1u);

  const auto* cfg = target.configs[0];
  EXPECT_EQ(cfg->name, "cfg");
  EXPECT_EQ(cfg->library, "rtlLib");
  ASSERT_EQ(cfg->design_cells.size(), 1u);
  EXPECT_EQ(cfg->design_cells[0].second, "top");
}

// §33.5.4: a config with several design cells and additional binding
// rules must come back from the archive in its entirety, since rule
// selection by the binding tool depends on every clause being intact.
// The §33.5.3 round-trip test only checks counts and library tags;
// here we exercise that the per-config descriptor — design cells and
// rule list — is preserved as well.
TEST(ConfigCommandLine, ConfigDesignCellsAndRulesRoundTrip) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "lib.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(
      "module a;\n"
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
