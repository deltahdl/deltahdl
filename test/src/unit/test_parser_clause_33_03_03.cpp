// Tests for IEEE 1800-2023 §33.3.3 "Mapping source files to libraries".
//
// The subclause owns two declarative rules, both applied at the parser stage by
// LibraryMap (src/parser/library_map.cpp):
//   - For each cell definition encountered during parsing, the name of the
//     source file being parsed is compared against the file path specifications
//     of the library declarations drawn from all of the library map files in
//     use (LibraryMap::TagCompilationUnit -> LibraryForFile).
//   - The cell is mapped into the library whose file path specification matches
//     the source file name (each cell's `library` tag is set to that library).
//
// The rule consumes constructs supplied by this pass's dependencies: the
// library declarations come from a real lib.map (§33.3.1) that may pull in
// further declarations via `include` (§33.3.2), and the cells come from real
// SystemVerilog source parsed by Parser::Parse(). Each test therefore builds
// both inputs from source on disk / in memory and drives them through the full
// parse-then-tag pipeline rather than hand-constructing AST nodes.

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
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/library_map.h"
#include "parser/parser.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

// Owns a unique scratch directory so both the lib.map and the source files a
// test names live on disk; the resolver anchors relative library specs to the
// map file's canonical directory, so the directory is canonicalized to keep the
// paths asserted on aligned with the loader's view.
struct ScratchDir {
  fs::path dir;

  ScratchDir() {
    static std::atomic<uint64_t> counter{0};
    auto seq = counter.fetch_add(1);
    dir = fs::temp_directory_path() /
          ("delta_map330303_" + std::to_string(::getpid()) + "_" +
           std::to_string(seq));
    fs::create_directories(dir);
    dir = fs::weakly_canonical(dir);
  }

  ~ScratchDir() {
    std::error_code ec;
    fs::remove_all(dir, ec);
  }

  fs::path Write(const std::string& rel, const std::string& content) {
    auto full = dir / rel;
    fs::create_directories(full.parent_path());
    std::ofstream ofs(full);
    ofs << content;
    return full;
  }
};

// Parses real SystemVerilog source into a CompilationUnit and keeps the backing
// SourceManager/Arena/DiagEngine alive so the parsed cells can be tagged and
// inspected. Stands in for the cells "encountered during parsing" that §33.3.3
// maps to libraries.
struct ParsedSource {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Arena arena;
  CompilationUnit* cu = nullptr;

  explicit ParsedSource(const std::string& text,
                        const std::string& name = "src.v") {
    uint32_t fid = mgr.AddFile(name, text);
    Lexer lexer(mgr.FileContent(fid), fid, diag);
    Parser parser(lexer, arena, diag);
    cu = parser.Parse();
  }
};

// "For each cell definition encountered during parsing": every kind of design
// element the parser can produce -- module, interface, program, checker,
// primitive (UDP), package, and config -- is compared against the mapping and
// tagged with the matching library, not just the module the example shows.
TEST(MapSourceFilesToLibraries, MapsEveryCellKindEncounteredDuringParsing) {
  ScratchDir tmp;
  auto map_file = tmp.Write("lib.map", "library L *.sv;\n");
  auto src = tmp.Write("all.sv", "");

  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(map_file));

  ParsedSource parsed(
      "module top; endmodule\n"
      "interface intf; endinterface\n"
      "program prog; endprogram\n"
      "checker chk; endchecker\n"
      "primitive prim(output out, input in);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n"
      "package pkg; endpackage\n"
      "config cfg; design top; endconfig\n");
  ASSERT_FALSE(parsed.diag.HasErrors());
  ASSERT_EQ(parsed.cu->modules.size(), 1u);
  ASSERT_EQ(parsed.cu->interfaces.size(), 1u);
  ASSERT_EQ(parsed.cu->programs.size(), 1u);
  ASSERT_EQ(parsed.cu->checkers.size(), 1u);
  ASSERT_EQ(parsed.cu->udps.size(), 1u);
  ASSERT_EQ(parsed.cu->packages.size(), 1u);
  ASSERT_EQ(parsed.cu->configs.size(), 1u);

  m.TagCompilationUnit(*parsed.cu, src.string());

  EXPECT_EQ(parsed.cu->modules[0]->library, "L");
  EXPECT_EQ(parsed.cu->interfaces[0]->library, "L");
  EXPECT_EQ(parsed.cu->programs[0]->library, "L");
  EXPECT_EQ(parsed.cu->checkers[0]->library, "L");
  EXPECT_EQ(parsed.cu->udps[0]->library, "L");
  EXPECT_EQ(parsed.cu->packages[0]->library, "L");
  EXPECT_EQ(parsed.cu->configs[0]->library, "L");
}

// "...in all of the library map files being used": the comparison spans
// declarations pulled in from an included map file, not only the root map. A
// cell whose source matches a spec declared in the included file is mapped into
// that included library.
TEST(MapSourceFilesToLibraries, MapsCellUsingDeclarationFromIncludedMapFile) {
  ScratchDir tmp;
  tmp.Write("sub.map", "library subLib *.sv;\n");
  auto top = tmp.Write("top.map",
                       "library topLib *.v;\n"
                       "include sub.map;\n");
  auto src = tmp.Write("dut.sv", "module dut; endmodule\n");

  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));

  ParsedSource parsed("module dut; endmodule\n");
  ASSERT_FALSE(parsed.diag.HasErrors());
  ASSERT_EQ(parsed.cu->modules.size(), 1u);

  m.TagCompilationUnit(*parsed.cu, src.string());
  EXPECT_EQ(parsed.cu->modules[0]->library, "subLib");
}

// "...in all of the library map files being used": the map information may be
// supplied as several independent files named for one invocation, read in turn,
// rather than gathered through an include. Two lib.map files loaded in sequence
// stand in for two files named at invocation; a cell whose source matches a
// declaration contributed by the second file is mapped into that file's
// library, confirming the comparison spans every loaded map file, not just the
// first.
TEST(MapSourceFilesToLibraries,
     MapsCellUsingDeclarationFromSeparatelyLoadedMapFile) {
  ScratchDir tmp;
  auto first = tmp.Write("a/lib.map", "library alpha *.v;\n");
  auto second = tmp.Write("b/lib.map", "library beta *.sv;\n");
  auto src = tmp.Write("b/dut.sv", "module dut; endmodule\n");

  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(first));
  ASSERT_TRUE(m.LoadMapFile(second));

  ParsedSource parsed("module dut; endmodule\n");
  ASSERT_FALSE(parsed.diag.HasErrors());
  ASSERT_EQ(parsed.cu->modules.size(), 1u);

  m.TagCompilationUnit(*parsed.cu, src.string());
  EXPECT_EQ(parsed.cu->modules[0]->library, "beta");
}

// The comparison is against the source file name of each unit independently:
// two source files matching two different declarations are mapped into their
// respective libraries when tagged with their own paths.
TEST(MapSourceFilesToLibraries, MapsEachSourceFileByItsOwnName) {
  ScratchDir tmp;
  auto map_file = tmp.Write("lib.map",
                            "library rtl *.v;\n"
                            "library gates *.vg;\n");
  auto rtl_src = tmp.Write("top.v", "module top; endmodule\n");
  auto gate_src = tmp.Write("top.vg", "module top; endmodule\n");

  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(map_file));

  ParsedSource rtl("module top; endmodule\n");
  ParsedSource gate("module top; endmodule\n");
  ASSERT_EQ(rtl.cu->modules.size(), 1u);
  ASSERT_EQ(gate.cu->modules.size(), 1u);

  m.TagCompilationUnit(*rtl.cu, rtl_src.string());
  m.TagCompilationUnit(*gate.cu, gate_src.string());

  EXPECT_EQ(rtl.cu->modules[0]->library, "rtl");
  EXPECT_EQ(gate.cu->modules[0]->library, "gates");
}

}  // namespace
