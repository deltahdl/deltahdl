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
          ("delta_precomp_elab_" + std::to_string(::getpid()) + "_" +
           std::to_string(seq));
    fs::create_directories(dir);
  }

  ~TempPrecompDir() {
    std::error_code ec;
    fs::remove_all(dir, ec);
  }
};

TEST(SeparateCompilationToolDescend, TransitiveDescentThroughLibrary) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  ASSERT_TRUE(
      PrecompiledLibrary::Save("module leaf;\n"
                               "endmodule\n",
                               "rtlLib", path));
  ASSERT_TRUE(
      PrecompiledLibrary::Save("module mid;\n"
                               "  leaf l();\n"
                               "endmodule\n",
                               "rtlLib", path));

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);

  std::string top_src =
      "module top;\n"
      "  mid m();\n"
      "endmodule\n";
  uint32_t fid = mgr.AddFile("<top>", top_src);
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());

  ASSERT_TRUE(PrecompiledLibrary::Load(path, *cu, mgr, arena, diag));
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate("top");
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->all_modules.size(), 3u);
  EXPECT_TRUE(design->all_modules.contains("top"));
  EXPECT_TRUE(design->all_modules.contains("mid"));
  EXPECT_TRUE(design->all_modules.contains("leaf"));
}

TEST(SeparateCompilationToolDescend, BindingFailsWhenLibraryMissingCell) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  ASSERT_TRUE(
      PrecompiledLibrary::Save("module other;\n"
                               "endmodule\n",
                               "rtlLib", path));

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);

  std::string top_src =
      "module top;\n"
      "  child c();\n"
      "endmodule\n";
  uint32_t fid = mgr.AddFile("<top>", top_src);
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());

  ASSERT_TRUE(PrecompiledLibrary::Load(path, *cu, mgr, arena, diag));
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab(arena, diag, cu);
  elab.Elaborate("top");
  EXPECT_TRUE(diag.HasErrors());
}

}  // namespace
