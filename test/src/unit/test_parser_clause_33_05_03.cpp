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

// Per-test scratch directory so concurrent runs do not collide on the
// shared system temp area.
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

// §33.5.3: "the compiled forms shall... exist somewhere in the
// filesystem."  After Save returns, a non-empty file is on disk at the
// path the caller asked for so that a later binding-tool invocation
// can find it.
TEST(SeparateCompilationTool, CompiledFormPersistsOnFilesystem) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(
      "module child;\n"
      "endmodule\n",
      "rtlLib", path));
  ASSERT_TRUE(fs::exists(path));
  EXPECT_GT(fs::file_size(path), 0u);
}

// §33.5.3: "the source descriptions shall be parsed and compiled into
// the library using one or more invocations of the compiler tool."
// Two separate Save calls — modeling two compiler invocations — build
// the library up incrementally.  A single Load surfaces every cell.
TEST(SeparateCompilationTool, MultipleInvocationsAccumulateCells) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(
      "module a;\n"
      "endmodule\n",
      "rtlLib", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(
      "module b;\n"
      "endmodule\n",
      "rtlLib", path));

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  CompilationUnit target;
  ASSERT_TRUE(PrecompiledLibrary::Load(path, target, mgr, arena, diag));
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(target.modules.size(), 2u);
  EXPECT_EQ(target.modules[0]->name, "a");
  EXPECT_EQ(target.modules[1]->name, "b");
}

// §33.5.3: "all cells in a design shall be precompiled prior to
// binding the design."  Save refuses to persist a cell that does not
// parse, which guarantees that anything the binding tool later reads
// from the library went through the compiler step.
TEST(SeparateCompilationTool, SaveRejectsUnparseableSource) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  EXPECT_FALSE(PrecompiledLibrary::Save(
      "module broken; this is not legal SystemVerilog\n",
      "rtlLib", path));
}

// §33.5.3: every cell-kind design element (modules, interfaces,
// programs, primitives, packages, configurations) is a candidate for
// precompilation; round-tripping each kind through Save/Load preserves
// the library tag and the cell's identity so the binding tool can
// resolve any of them.
TEST(SeparateCompilationTool, AllCellKindsRoundTrip) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(
      "module m;\n"
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

// §33.5.3: the format and location are tool-specific, so the file is
// not interchangeable with arbitrary bytes; loading a path that lacks
// the tool-specific marker fails cleanly.
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

// §33.5.3: a missing precompiled library is also a hard failure — the
// binding tool cannot manufacture cells out of thin air.
TEST(SeparateCompilationTool, LoadFailsForMissingFile) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "does_not_exist.dpl";
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  CompilationUnit target;
  EXPECT_FALSE(PrecompiledLibrary::Load(path, target, mgr, arena, diag));
}

// §33.5.3: each invocation of the compiler tool tags its chunk with
// the library it is populating.  Two invocations targeting different
// libraries — sharing one on-disk archive — must keep their library
// identifiers separate so the binding tool can later resolve cells in
// the right library.
TEST(SeparateCompilationTool, MultipleLibrariesPreserveTagsIndependently) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "shared.dpl";
  ASSERT_TRUE(PrecompiledLibrary::Save(
      "module a;\n"
      "endmodule\n",
      "libA", path));
  ASSERT_TRUE(PrecompiledLibrary::Save(
      "module b;\n"
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

// §33.5.3: a corrupted on-disk library cannot be silently absorbed.
// Crafting a file that has the right magic but a chunk header pointing
// past end-of-file models a partial write or transport corruption; the
// loader must reject it rather than hand the binding tool a fragmentary
// view of the library.
TEST(SeparateCompilationTool, LoadFailsOnTruncatedChunk) {
  TempPrecompDir tmp;
  auto path = tmp.dir / "truncated.dpl";
  std::ofstream os(path, std::ios::binary);
  os.write("DPLIB001", 8);
  // A library_name length of 16 with no body bytes available.
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
