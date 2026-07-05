// Tests for IEEE 1800-2023 §33.4.1.1 "Design statement".
//
// The subclause layers semantic requirements on top of the design_statement
// production owned by §33.4.1. Two of those requirements are applied at the
// elaboration stage by Elaborator::ValidateConfigDesignStatements
// (src/elaborator/elaborator_validate_config.cpp):
//   - The cell or cells a design statement names cannot themselves be configs;
//     a name that also denotes a real cell is accepted (the cell wins over a
//     like-named config).
//   - When a design cell omits its library qualifier, the library that contains
//     the config is used to search for the cell.
//
// The omitted-library rule consumes an input produced by this pass's
// dependencies §33.3.1/§33.3.3: a config's `library` tag is not intrinsic to
// the config's own syntax — it is assigned by the library-map machinery
// (LibraryMap::TagCompilationUnit -> LibraryForFile) from a real lib.map. The
// library tests below therefore build that library from a lib.map on disk and
// drive it through the full parse-then-tag-then-elaborate pipeline rather than
// hand-assigning the config's `library` field.

#include <unistd.h>

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>

#include "fixture_elaborator.h"
#include "parser/library_map.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

// Owns a unique scratch directory so the lib.map and the source file a test
// names live on disk; the map resolver anchors relative library specs to the
// map file's canonical directory, so the directory is canonicalized to keep the
// tagged path aligned with the loader's view. Mirrors the idiom used by the
// §33.3.1/§33.3.3 dependency tests that exercise the same machinery.
struct ScratchDir {
  fs::path dir;

  ScratchDir() {
    static std::atomic<uint64_t> counter{0};
    auto seq = counter.fetch_add(1);
    dir = fs::temp_directory_path() /
          ("delta_map330401_" + std::to_string(::getpid()) + "_" +
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

TEST(ConfigDesignStatement, DesignCellNamingConfigIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module dummy; endmodule\n"
      "config inner;\n"
      "  design dummy;\n"
      "endconfig\n"
      "config outer;\n"
      "  design inner;\n"
      "endconfig\n",
      f, "dummy");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConfigDesignStatement,
     DesignCellNamingConfigAmongMultipleCellsIsRejected) {
  // §33.4.1.1: the no-config rule applies to every cell a design statement
  // lists, not only the first. Here 'outer' names a real module and, as a
  // second cell, a name that denotes only a config ('sub'); the config-named
  // cell must be rejected even though the design statement is otherwise valid.
  ElabFixture f;
  ElaborateSrc(
      "module m; endmodule\n"
      "config sub;\n"
      "  design m;\n"
      "endconfig\n"
      "config outer;\n"
      "  design m sub;\n"
      "endconfig\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConfigDesignStatement, ProgramSharingNameWithConfigIsAccepted) {
  // §33.4.1.1: a design cell that shares its name with a config is not limited
  // to modules -- any top-level design element wins over a like-named config.
  // Here a program and a config are both named 'shared'; the design naming
  // 'shared' denotes the program and must be accepted. The config is placed in
  // a separate library so program and config do not collide under the
  // duplicate-definition check; a benign module is the elaboration top.
  delta::SourceManager mgr;
  delta::Arena arena;
  delta::DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>",
                         "module top; endmodule\n"
                         "program shared; endprogram\n"
                         "config shared;\n"
                         "  design shared;\n"
                         "endconfig\n");
  delta::Lexer lexer(mgr.FileContent(fid), fid, diag);
  delta::Parser parser(lexer, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->configs.size(), 1u);

  cu->configs[0]->library = "altLib";

  delta::Elaborator elab(arena, diag, cu);
  elab.Elaborate("top");
  EXPECT_FALSE(diag.HasErrors());
}

TEST(ConfigDesignStatement, DesignCellSharingNameWithConfigIsAccepted) {
  // §33.4.1.1: a design cell may carry the same name as a config. Here a module
  // and a config both named 'shared' exist; the design statement names
  // 'shared', which denotes the module, not the config, and must be accepted.
  // The library the config carries is not the input this rule consumes — it is
  // present only so the config and the like-named module land in different
  // libraries and do not trip the unrelated duplicate-definition check. A
  // single merged compilation unit is tagged with one library by the map
  // machinery, so the two libraries are assigned directly here.
  delta::SourceManager mgr;
  delta::Arena arena;
  delta::DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>",
                         "module shared; endmodule\n"
                         "config shared;\n"
                         "  design shared;\n"
                         "endconfig\n");
  delta::Lexer lexer(mgr.FileContent(fid), fid, diag);
  delta::Parser parser(lexer, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->configs.size(), 1u);

  cu->configs[0]->library = "altLib";

  delta::Elaborator elab(arena, diag, cu);
  elab.Elaborate("shared");
  EXPECT_FALSE(diag.HasErrors());
}

TEST(ConfigDesignStatement, OmittedLibraryDefaultsToConfigLibrary) {
  // §33.4.1.1: when a design cell omits its library qualifier, the library that
  // contains the config supplies the library used to find the cell. The
  // config's library is produced by this pass's dependency §33.3.1/§33.3.3 — a
  // real lib.map maps the config's source file into library 'myLib' — so the
  // rule is observed consuming a library assigned by the parse-then-tag
  // pipeline, not one hand-written onto the config.
  ScratchDir tmp;
  auto map_file = tmp.Write("lib.map", "library myLib *.v;\n");
  std::string source =
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "endconfig\n";
  auto src = tmp.Write("top.v", source);

  delta::LibraryMap lib_map;
  ASSERT_TRUE(lib_map.LoadMapFile(map_file));

  delta::SourceManager mgr;
  delta::Arena arena;
  delta::DiagEngine diag(mgr);
  auto fid = mgr.AddFile(src.string(), source);
  delta::Lexer lexer(mgr.FileContent(fid), fid, diag);
  delta::Parser parser(lexer, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->configs.size(), 1u);

  // The library-map machinery assigns the config its 'myLib' library from the
  // source file's path, exactly as §33.3.3 maps a source file to its library.
  lib_map.TagCompilationUnit(*cu, src.string());
  ASSERT_EQ(cu->configs[0]->library, "myLib");

  delta::Elaborator elab(arena, diag, cu);
  elab.Elaborate("top");
  EXPECT_FALSE(diag.HasErrors());

  ASSERT_EQ(cu->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(cu->configs[0]->design_cells[0].first, "myLib");
  EXPECT_EQ(cu->configs[0]->design_cells[0].second, "top");
}

TEST(ConfigDesignStatement, ExplicitLibraryIsNotOverridden) {
  // §33.4.1.1: the config's own library is substituted only when the design
  // cell omits its library qualifier. Here the design names 'work.top' with an
  // explicit qualifier, so the config's own library ('otherLib', assigned by
  // the real lib.map machinery) must not override it; the explicit qualifier
  // survives elaboration unchanged.
  ScratchDir tmp;
  auto map_file = tmp.Write("lib.map", "library otherLib *.v;\n");
  std::string source =
      "module top; endmodule\n"
      "config c;\n"
      "  design work.top;\n"
      "endconfig\n";
  auto src = tmp.Write("top.v", source);

  delta::LibraryMap lib_map;
  ASSERT_TRUE(lib_map.LoadMapFile(map_file));

  delta::SourceManager mgr;
  delta::Arena arena;
  delta::DiagEngine diag(mgr);
  auto fid = mgr.AddFile(src.string(), source);
  delta::Lexer lexer(mgr.FileContent(fid), fid, diag);
  delta::Parser parser(lexer, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->configs.size(), 1u);

  lib_map.TagCompilationUnit(*cu, src.string());
  ASSERT_EQ(cu->configs[0]->library, "otherLib");

  delta::Elaborator elab(arena, diag, cu);
  elab.Elaborate("top");
  EXPECT_FALSE(diag.HasErrors());

  ASSERT_EQ(cu->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(cu->configs[0]->design_cells[0].first, "work");
  EXPECT_EQ(cu->configs[0]->design_cells[0].second, "top");
}

TEST(ConfigDesignStatement, MixedOmittedAndExplicitLibrariesResolvedPerCell) {
  // §33.4.1.1: the omitted-library substitution is applied independently to
  // each cell. A design statement listing one bare cell and one
  // library-qualified cell resolves the bare cell to the config's library while
  // leaving the explicit qualifier untouched. The config's library is produced
  // by the dependency lib.map machinery (§33.3.1/§33.3.3), not hand-assigned.
  ScratchDir tmp;
  auto map_file = tmp.Write("lib.map", "library myLib *.v;\n");
  std::string source =
      "module c; endmodule\n"
      "module d; endmodule\n"
      "config cfg;\n"
      "  design c work.d;\n"
      "endconfig\n";
  auto src = tmp.Write("top.v", source);

  delta::LibraryMap lib_map;
  ASSERT_TRUE(lib_map.LoadMapFile(map_file));

  delta::SourceManager mgr;
  delta::Arena arena;
  delta::DiagEngine diag(mgr);
  auto fid = mgr.AddFile(src.string(), source);
  delta::Lexer lexer(mgr.FileContent(fid), fid, diag);
  delta::Parser parser(lexer, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(diag.HasErrors());
  ASSERT_EQ(cu->configs.size(), 1u);

  lib_map.TagCompilationUnit(*cu, src.string());
  ASSERT_EQ(cu->configs[0]->library, "myLib");

  delta::Elaborator elab(arena, diag, cu);
  elab.Elaborate("c");
  EXPECT_FALSE(diag.HasErrors());

  ASSERT_EQ(cu->configs[0]->design_cells.size(), 2u);
  EXPECT_EQ(cu->configs[0]->design_cells[0].first, "myLib");
  EXPECT_EQ(cu->configs[0]->design_cells[0].second, "c");
  EXPECT_EQ(cu->configs[0]->design_cells[1].first, "work");
  EXPECT_EQ(cu->configs[0]->design_cells[1].second, "d");
}

}  // namespace
