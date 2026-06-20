#include <gtest/gtest.h>
#include <unistd.h>

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <fstream>
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
          ("delta_precomp_" + std::to_string(::getpid()) + "_" +
           std::to_string(seq));
    fs::create_directories(dir);
  }

  ~TempPrecompDir() {
    std::error_code ec;
    fs::remove_all(dir, ec);
  }
};

TEST(SeparateCompilationTool, CompiledFormPersistsOnFilesystem) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  ASSERT_TRUE(
      PrecompiledLibrary::Save("module child;\n"
                               "endmodule\n",
                               "rtlLib", path));
  ASSERT_TRUE(fs::exists(path));
  EXPECT_GT(fs::file_size(path), 0u);
}

TEST(SeparateCompilationTool, SaveRejectsUnparseableSource) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  EXPECT_FALSE(PrecompiledLibrary::Save(
      "module broken; this is not legal SystemVerilog\n", "rtlLib", path));
}

// The compiled form has to land somewhere in the filesystem; if the chosen
// location cannot hold it (here, a parent directory that does not exist), the
// save reports failure rather than silently discarding the cell. The source is
// well-formed so the failure is attributable to the location, not the parse.
TEST(SeparateCompilationTool, SaveFailsWhenLocationUnwritable) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "missing_subdir" / "rtlLib.dpl";
  EXPECT_FALSE(
      PrecompiledLibrary::Save("module child;\n"
                               "endmodule\n",
                               "rtlLib", path));
  std::error_code ec;
  EXPECT_FALSE(fs::exists(path, ec));
}

TEST(SeparateCompilationTool, AllCellKindsRoundTrip) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  ASSERT_TRUE(
      PrecompiledLibrary::Save("module m;\n"
                               "endmodule\n"
                               "interface i;\n"
                               "endinterface\n"
                               "program p;\n"
                               "endprogram\n"
                               "primitive u(output o, input a);\n"
                               "  table\n"
                               "    0 : 0;\n"
                               "    1 : 1;\n"
                               "  endtable\n"
                               "endprimitive\n"
                               "package pk;\n"
                               "endpackage\n"
                               "config cfg;\n"
                               "  design m;\n"
                               "endconfig\n",
                               "rtlLib", path));

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  CompilationUnit target;
  ASSERT_TRUE(PrecompiledLibrary::Load(path, target, mgr, arena, diag));
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(target.modules.size(), 1u);
  ASSERT_EQ(target.interfaces.size(), 1u);
  ASSERT_EQ(target.programs.size(), 1u);
  ASSERT_EQ(target.udps.size(), 1u);
  ASSERT_EQ(target.packages.size(), 1u);
  ASSERT_EQ(target.configs.size(), 1u);
  EXPECT_EQ(target.modules[0]->library, "rtlLib");
  EXPECT_EQ(target.interfaces[0]->library, "rtlLib");
  EXPECT_EQ(target.programs[0]->library, "rtlLib");
  EXPECT_EQ(target.udps[0]->library, "rtlLib");
  EXPECT_EQ(target.packages[0]->library, "rtlLib");
  EXPECT_EQ(target.configs[0]->library, "rtlLib");
}

TEST(SeparateCompilationTool, LoadRejectsAlienFile) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "alien.bin";
  std::ofstream(path) << "not a precompiled library";

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  CompilationUnit target;
  EXPECT_FALSE(PrecompiledLibrary::Load(path, target, mgr, arena, diag));
}

TEST(SeparateCompilationTool, LoadFailsForMissingFile) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "does_not_exist.dpl";
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  CompilationUnit target;
  EXPECT_FALSE(PrecompiledLibrary::Load(path, target, mgr, arena, diag));
}

TEST(SeparateCompilationTool, MultipleLibrariesPreserveTagsIndependently) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "shared.dpl";
  ASSERT_TRUE(
      PrecompiledLibrary::Save("module a;\n"
                               "endmodule\n",
                               "libA", path));
  ASSERT_TRUE(
      PrecompiledLibrary::Save("module b;\n"
                               "endmodule\n",
                               "libB", path));

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  CompilationUnit target;
  ASSERT_TRUE(PrecompiledLibrary::Load(path, target, mgr, arena, diag));
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(target.modules.size(), 2u);
  EXPECT_EQ(target.modules[0]->name, "a");
  EXPECT_EQ(target.modules[0]->library, "libA");
  EXPECT_EQ(target.modules[1]->name, "b");
  EXPECT_EQ(target.modules[1]->library, "libB");
}

TEST(SeparateCompilationTool, LoadFailsOnTruncatedChunk) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "truncated.dpl";
  std::ofstream os(path, std::ios::binary);
  os.write("DPLIB001", 8);

  unsigned char bad[4] = {0x10, 0x00, 0x00, 0x00};
  os.write(reinterpret_cast<const char*>(bad), 4);
  os.close();

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  CompilationUnit target;
  EXPECT_FALSE(PrecompiledLibrary::Load(path, target, mgr, arena, diag));
}

}  // namespace
