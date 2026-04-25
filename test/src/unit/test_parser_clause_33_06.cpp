#include <gtest/gtest.h>
#include <unistd.h>

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>

#include "parser/ast.h"
#include "parser/library_map.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

// Per-test scratch directory so the §33.6 example can be staged on disk
// and compiled through LoadMapFile end-to-end.
struct TempDir {
  fs::path dir;

  TempDir() {
    static std::atomic<uint64_t> counter{0};
    auto seq = counter.fetch_add(1);
    dir = fs::temp_directory_path() /
          ("delta_clause33_06_" + std::to_string(::getpid()) + "_" +
           std::to_string(seq));
    fs::create_directories(dir);
  }

  ~TempDir() {
    std::error_code ec;
    fs::remove_all(dir, ec);
  }

  fs::path Write(const std::string& rel, const std::string& content) {
    auto full = dir / rel;
    std::ofstream ofs(full);
    ofs << content;
    return full;
  }
};

// The exact lib.map shown in §33.6 — kept verbatim (including the line
// break before adder.vg) so the test is unmistakably the LRM example.
constexpr const char* kExampleLibMap =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library gateLib\n"
    "    adder.vg;\n";

// §33.6 enumerates the resulting library structure at cell granularity:
// rtlLib.top + rtlLib.m from top.v, aLib.adder + aLib.m from adder.v,
// gateLib.adder + gateLib.m from adder.vg.  Stage each compilation unit
// with the modules its source contributes and confirm every cell ends
// up under the library §33.6 names for it.
TEST(ConfigurationExample, TaggingYieldsExampleLibraryStructure) {
  TempDir tmp;
  auto map_file = tmp.Write("lib.map", kExampleLibMap);

  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(map_file));

  // top.v contributes module top and module m.
  CompilationUnit cu_top;
  ModuleDecl top_top;
  top_top.name = "top";
  ModuleDecl top_m;
  top_m.name = "m";
  cu_top.modules.push_back(&top_top);
  cu_top.modules.push_back(&top_m);
  m.TagCompilationUnit(cu_top, (tmp.dir / "top.v").string());

  // adder.v contributes module adder and module m (rtl view).
  CompilationUnit cu_adder_v;
  ModuleDecl adder_v_adder;
  adder_v_adder.name = "adder";
  ModuleDecl adder_v_m;
  adder_v_m.name = "m";
  cu_adder_v.modules.push_back(&adder_v_adder);
  cu_adder_v.modules.push_back(&adder_v_m);
  m.TagCompilationUnit(cu_adder_v, (tmp.dir / "adder.v").string());

  // adder.vg contributes module adder and module m (gate view).
  CompilationUnit cu_adder_vg;
  ModuleDecl adder_vg_adder;
  adder_vg_adder.name = "adder";
  ModuleDecl adder_vg_m;
  adder_vg_m.name = "m";
  cu_adder_vg.modules.push_back(&adder_vg_adder);
  cu_adder_vg.modules.push_back(&adder_vg_m);
  m.TagCompilationUnit(cu_adder_vg, (tmp.dir / "adder.vg").string());

  EXPECT_EQ(top_top.library, "rtlLib");        // rtlLib.top
  EXPECT_EQ(top_m.library, "rtlLib");          // rtlLib.m
  EXPECT_EQ(adder_v_adder.library, "aLib");    // aLib.adder
  EXPECT_EQ(adder_v_m.library, "aLib");        // aLib.m
  EXPECT_EQ(adder_vg_adder.library, "gateLib");  // gateLib.adder
  EXPECT_EQ(adder_vg_m.library, "gateLib");      // gateLib.m
}

}  // namespace
