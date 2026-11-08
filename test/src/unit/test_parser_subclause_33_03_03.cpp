#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_scratch_dir.h"
#include "lexer/lexer.h"
#include "parser/library_map.h"
#include "parser/parser.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

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
