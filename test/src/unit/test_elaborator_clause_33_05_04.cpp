#include <gtest/gtest.h>
#include <unistd.h>

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
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
          ("delta_clause_33_05_04_" + std::to_string(::getpid()) + "_" +
           std::to_string(seq));
    fs::create_directories(dir);
  }
  ~TempPrecompDir() {
    std::error_code ec;
    fs::remove_all(dir, ec);
  }
};

CompilationUnit* ParseSrc(SourceManager& mgr, Arena& arena, DiagEngine& diag,
                          std::string src) {
  auto fid = mgr.AddFile("<test>", std::move(src));
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  return parser.Parse();
}

// §33.5.4: when a config carries a design statement, the named cell is the
// top-level module and uninstantiated cells elsewhere in the sources do not
// become tops. The elaborator builds the top set strictly from the config's
// design cells, so the spurious modules are never elaborated.
TEST(ConfigCommandLine, UninstantiatedCellsDoNotDisplaceDesignTop) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseSrc(mgr, arena, diag,
                      "module spurious_a;\n"
                      "endmodule\n"
                      "module spurious_b;\n"
                      "endmodule\n"
                      "module my_top;\n"
                      "endmodule\n"
                      "config cfg;\n"
                      "  design my_top;\n"
                      "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "my_top");
  EXPECT_FALSE(design->all_modules.contains("spurious_a"));
  EXPECT_FALSE(design->all_modules.contains("spurious_b"));
}

TEST(ConfigCommandLine, MultipleDesignCellsAllBecomeTopModules) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto* cu = ParseSrc(mgr, arena, diag,
                      "module a;\n"
                      "endmodule\n"
                      "module b;\n"
                      "endmodule\n"
                      "config cfg;\n"
                      "  design a b;\n"
                      "endconfig\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->name, "a");
  EXPECT_EQ(design->top_modules[1]->name, "b");
}

TEST(ConfigCommandLine, PrecompiledConfigDrivesBinding) {
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
  CompilationUnit cu;
  ASSERT_TRUE(PrecompiledLibrary::Load(path, cu, mgr, arena, diag));
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu.configs.size(), 1u);
  ASSERT_EQ(cu.modules.size(), 1u);

  Elaborator elab(arena, diag, &cu);
  auto* design = elab.Elaborate(cu.configs[0]);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

}
