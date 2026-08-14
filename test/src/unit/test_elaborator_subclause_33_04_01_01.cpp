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

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/separate_compilation_bind.h"
#include "fixture_config_unit.h"
#include "fixture_elaborator.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"
#include "parser/library_map.h"
#include "parser/precompiled_library.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

// Owns a unique scratch directory so the lib.map and the source file a test
// names live on disk; the map resolver anchors relative library specs to the
// map file's canonical directory, so the directory is canonicalized to keep the
// tagged path aligned with the loader's view. Mirrors the idiom used by the
// §33.3.1/§33.3.3 dependency tests that exercise the same machinery.

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
  // Elaborator::ValidateConfigDesignStatements reports at the design cell it
  // is about, which is on the design statement on line 6, not at the `config`
  // keyword on line 5.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'outer' design statement names "
                            "configuration 'inner'; design cells must not be "
                            "configs",
                            6, "33.4.1.1"));
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
  // The report names the second cell 'sub' rather than the first cell 'm',
  // which is what says the rule reached past the head of the list. It stands at
  // the design statement on line 6, where the offending cell is written.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'outer' design statement names "
                            "configuration 'sub'; design cells must not be "
                            "configs",
                            6, "33.4.1.1"));
}

// §33.4.1.1 admits any number of cells in one design statement, so the report
// has to say which of them it is about. Three cells are written on three lines
// and the offending one is last, because a design statement whose cells share
// a line makes the cell's position and the statement's position the same
// number and would pass whether the report moved or not.
TEST(ConfigDesignStatement, ReportStandsAtTheOffendingDesignCell) {
  ElabFixture f;
  ElaborateSrc(
      "module first; endmodule\n"
      "module second; endmodule\n"
      "config sub;\n"
      "  design first;\n"
      "endconfig\n"
      "config outer;\n"
      "  design first\n"
      "         second\n"
      "         sub;\n"
      "endconfig\n",
      f, "first");
  // Line 9 holds 'sub' alone. Line 6 is the `config` keyword and line 7 the
  // head of the design statement, so an assertion naming 9 fails on either of
  // the two positions this report used to be able to carry.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'outer' design statement names "
                            "configuration 'sub'; design cells must not be "
                            "configs",
                            9, "33.4.1.1"));
}

TEST(ConfigDesignStatement, ProgramSharingNameWithConfigIsAccepted) {
  // §33.4.1.1: a design cell that shares its name with a config is not limited
  // to modules -- any top-level design element wins over a like-named config.
  // Here a program and a config are both named 'shared'; the design naming
  // 'shared' denotes the program and must be accepted. The config is placed in
  // a separate library so program and config do not collide under the
  // duplicate-definition check; a benign module is the elaboration top.
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module top; endmodule\n"
              "program shared; endprogram\n"
              "config shared;\n"
              "  design shared;\n"
              "endconfig\n"));
  u.PlaceConfigInLibrary("altLib");
  u.ElaborateTop("top");
  EXPECT_FALSE(u.diag.HasErrors());
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
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module shared; endmodule\n"
              "config shared;\n"
              "  design shared;\n"
              "endconfig\n"));
  u.PlaceConfigInLibrary("altLib");
  u.ElaborateTop("shared");
  EXPECT_FALSE(u.diag.HasErrors());
}

TEST(ConfigDesignStatement, OmittedLibraryDefaultsToConfigLibrary) {
  // §33.4.1.1: when a design cell omits its library qualifier, the library that
  // contains the config supplies the library used to find the cell. The
  // config's library is produced by this pass's dependency §33.3.1/§33.3.3 — a
  // real lib.map maps the config's source file into library 'myLib' — so the
  // rule is observed consuming a library assigned by the parse-then-tag
  // pipeline, not one hand-written onto the config.
  ScratchDir tmp;
  MappedConfigUnit u;
  ASSERT_TRUE(u.ParseUnderMap(tmp, "library myLib *.v;\n",
                              "module top; endmodule\n"
                              "config c;\n"
                              "  design top;\n"
                              "endconfig\n"));
  // The library-map machinery assigns the config its 'myLib' library from the
  // source file's path, exactly as §33.3.3 maps a source file to its library.
  ASSERT_EQ(u.ConfigLibrary(), "myLib");
  u.ElaborateTop("top");
  EXPECT_FALSE(u.diag.HasErrors());

  ASSERT_EQ(u.cu->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(u.cu->configs[0]->design_cells[0].library, "myLib");
  EXPECT_EQ(u.cu->configs[0]->design_cells[0].cell, "top");
}

TEST(ConfigDesignStatement, ExplicitLibraryIsNotOverridden) {
  // §33.4.1.1: the config's own library is substituted only when the design
  // cell omits its library qualifier. Here the design names 'work.top' with an
  // explicit qualifier, so the config's own library ('otherLib', assigned by
  // the real lib.map machinery) must not override it; the explicit qualifier
  // survives elaboration unchanged.
  ScratchDir tmp;
  MappedConfigUnit u;
  ASSERT_TRUE(u.ParseUnderMap(tmp, "library otherLib *.v;\n",
                              "module top; endmodule\n"
                              "config c;\n"
                              "  design work.top;\n"
                              "endconfig\n"));
  ASSERT_EQ(u.ConfigLibrary(), "otherLib");
  u.ElaborateTop("top");
  EXPECT_FALSE(u.diag.HasErrors());

  ASSERT_EQ(u.cu->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(u.cu->configs[0]->design_cells[0].library, "work");
  EXPECT_EQ(u.cu->configs[0]->design_cells[0].cell, "top");
}

TEST(ConfigDesignStatement, MixedOmittedAndExplicitLibrariesResolvedPerCell) {
  // §33.4.1.1: the omitted-library substitution is applied independently to
  // each cell. A design statement listing one bare cell and one
  // library-qualified cell resolves the bare cell to the config's library while
  // leaving the explicit qualifier untouched. The config's library is produced
  // by the dependency lib.map machinery (§33.3.1/§33.3.3), not hand-assigned.
  ScratchDir tmp;
  MappedConfigUnit u;
  ASSERT_TRUE(u.ParseUnderMap(tmp, "library myLib *.v;\n",
                              "module c; endmodule\n"
                              "module d; endmodule\n"
                              "config cfg;\n"
                              "  design c work.d;\n"
                              "endconfig\n"));
  ASSERT_EQ(u.ConfigLibrary(), "myLib");
  u.ElaborateTop("c");
  EXPECT_FALSE(u.diag.HasErrors());

  ASSERT_EQ(u.cu->configs[0]->design_cells.size(), 2u);
  EXPECT_EQ(u.cu->configs[0]->design_cells[0].library, "myLib");
  EXPECT_EQ(u.cu->configs[0]->design_cells[0].cell, "c");
  EXPECT_EQ(u.cu->configs[0]->design_cells[1].library, "work");
  EXPECT_EQ(u.cu->configs[0]->design_cells[1].cell, "d");
}

// §33.4.1.1 writes a design statement's entry as
// `[ library_identifier . ] cell_identifier`, so a cell no library holds is
// reported at its own cell_identifier. The statement here names two cells on
// two lines, one that resolves and one that does not, which is what separates
// the cell's position from the design statement's and from the config
// declaration's: a report standing at either of those carries line 3 or line 2
// instead of line 4.
TEST(ConfigDesignStatement, DesignCellNoLibraryHoldsIsReportedAtThatCell) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module m; endmodule\n"
              "config cfg;\n"
              "  design m\n"
              "         missing;\n"
              "endconfig\n"));
  EXPECT_EQ(u.ElaborateConfig(0), nullptr);
  EXPECT_TRUE(ReportedError(u.diag.Diagnostics(),
                            "config 'cfg' design cell 'missing' not found", 4,
                            "33.4.1.1"));
}

// The infrastructure one bind runs against. A configuration reaches a bind
// already compiled, so the case writes it into a compiled form and reads it
// back rather than parsing a source description.
struct ConfigBindHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  SeparateCompilationBinder binder{mgr, arena, diag};
};

// §33.4.1.1 has the design statement name the top-level cells of the design, so
// a configuration whose statement names none describes no design to bind. The
// report is about the config declaration and stands at the `config` keyword,
// which line 3 here separates from the `design` statement on line 4 and from
// the start of the compiled source description on line 1.
TEST(ConfigDesignStatement, ConfigNamingNoDesignIsReportedAtItsDeclaration) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtl.dpl";
  ASSERT_TRUE(
      PrecompiledLibrary::Save("module top;\n"
                               "endmodule\n"
                               "config cfg_empty;\n"
                               "  design;\n"
                               "endconfig\n",
                               "rtlLib", path));

  ConfigBindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.BindConfig("cfg_empty"), nullptr);
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "config 'cfg_empty' names no design", 3,
                            "33.4.1.1"));
}

}  // namespace
