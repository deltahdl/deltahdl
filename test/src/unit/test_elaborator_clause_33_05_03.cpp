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

// §33.5.3: "the tool that actually does the binding only needs to be
// told the top-level module(s) of the design to be bound, and then it
// shall use the precompiled form of the cell description(s) from the
// library to determine the subinstances and descend hierarchically
// down the design, binding each cell as it is located."
//
// Two precompile-tool invocations populate the library with `mid`
// (which itself instantiates `leaf`) and `leaf`.  The binding-tool
// invocation parses only the top-level source, pulls both cells back
// from disk, and elaborates from the named top.  The descent has to
// walk through the precompiled `mid` to reach the precompiled `leaf`,
// so all three modules show up in the final design.
TEST(SeparateCompilationToolDescend, TransitiveDescentThroughLibrary) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(
      "module leaf;\n"
      "endmodule\n",
      "rtlLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(
      "module mid;\n"
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

// §33.5.3: the binding tool relies on the precompiled form to locate
// every subinstance, so when the library does not contain a needed
// cell the descent has nowhere to go and binding fails.  Save a
// stranger cell to disk, point the binding step at a top that
// instantiates a different name, and expect the elaborator to flag
// the missing entry rather than synthesize a stub.
TEST(SeparateCompilationToolDescend, BindingFailsWhenLibraryMissingCell) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(
      "module other;\n"
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
