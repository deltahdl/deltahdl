#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_scratch_dir.h"
#include "parser/ast.h"
#include "parser/library_map.h"
#include "parser/single_pass_compile.h"

using namespace delta;

namespace {

// §33.5.1 describes the traditional use model: the source descriptions a
// design may bind against are exactly the files named on the command line, a
// precompiling strategy parses each of them and maps every cell it declares
// into a library whether or not the design uses that cell, and a cell already
// held in its library from an unchanged description need not be compiled
// again.
//
// The libraries the cells are mapped into are the ones a §33.3.1 library map
// names, so each test writes a real lib.map and real source files to disk and
// drives them through LoadMapFile and the compiler rather than handing the
// compiler a hand-built library map. Library names other than the default are
// used throughout, so a cell landing in the wrong library is visible.

// The shared infrastructure a compile writes into, and the compiler that
// writes into it. Every piece has to outlive the compile, so they are held
// together rather than returned.
struct CompileHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap libs;
  CompilationUnit unit;
  SinglePassCompiler compiler{libs, mgr, arena, diag};
};

// ---------------------------------------------------------------------------
// Claim: a precompiling strategy parses every cell description named on the
// command line and maps it into the library, whether or not the cell is used.
// ---------------------------------------------------------------------------

TEST(SinglePassPrecompile, CellNoInstanceNamesIsStillMappedIntoItsLibrary) {
  ScratchDir tmp;
  tmp.Write("lib.map",
            "library rtlLib rtl/*.v;\n"
            "library gateLib gate/*.vg;\n");
  auto top = tmp.Write("rtl/top.v",
                       "module top;\n"
                       "  adder a1();\n"
                       "endmodule\n");
  auto gate = tmp.Write("gate/adder.vg",
                        "module adder;\n"
                        "endmodule\n"
                        "module spare_adder;\n"
                        "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({top, gate}, h.unit));

  // Nothing instantiates spare_adder; it reaches the library all the same.
  EXPECT_NE(h.libs.CellInLibrary("gateLib", "spare_adder"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("gateLib", "adder"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("rtlLib", "top"), nullptr);
  // Each cell lands in the library its own description maps to, not in the
  // one belonging to a description compiled beside it.
  EXPECT_EQ(h.libs.CellInLibrary("rtlLib", "spare_adder"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("gateLib", "top"), nullptr);
}

TEST(SinglePassPrecompile, CompiledCellsAccumulateIntoOneCompilationUnit) {
  // The cells of every description on the command line gather into the one
  // unit the design is later located and bound in.
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto one = tmp.Write("src/one.v",
                       "module one;\n"
                       "endmodule\n");
  auto two = tmp.Write("src/two.v",
                       "module two;\n"
                       "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({one, two}, h.unit));

  ASSERT_EQ(h.unit.modules.size(), 2u);
  EXPECT_EQ(h.unit.modules[0]->name, "one");
  EXPECT_EQ(h.unit.modules[1]->name, "two");
  EXPECT_EQ(h.unit.modules[0]->library, "rtlLib");
}

TEST(SinglePassPrecompile, NonModuleCellsKeepToTheirOwnDescriptionsLibrary) {
  // Two descriptions, each mapped to a library of its own, declaring cells of
  // the same five non-module kinds under the same five names. A cell reaching
  // the library its own file maps to is only observable when a second library
  // is standing by to receive it wrongly: were every cell tagged from one
  // description, half of these lookups would come back empty.
  ScratchDir tmp;
  tmp.Write("lib.map",
            "library alphaLib alpha/*.sv;\n"
            "library betaLib beta/*.sv;\n");
  auto a = tmp.Write("alpha/a.sv",
                     "module ma;\n"
                     "endmodule\n"
                     "interface iface;\n"
                     "endinterface\n"
                     "program prog;\n"
                     "endprogram\n"
                     "primitive prim(output o, input a);\n"
                     "  table\n"
                     "    0 : 0;\n"
                     "    1 : 1;\n"
                     "  endtable\n"
                     "endprimitive\n"
                     "package pkg;\n"
                     "endpackage\n"
                     "config cfg;\n"
                     "  design ma;\n"
                     "endconfig\n");
  auto b = tmp.Write("beta/b.sv",
                     "module mb;\n"
                     "endmodule\n"
                     "interface iface;\n"
                     "endinterface\n"
                     "program prog;\n"
                     "endprogram\n"
                     "primitive prim(output o, input a);\n"
                     "  table\n"
                     "    0 : 1;\n"
                     "    1 : 0;\n"
                     "  endtable\n"
                     "endprimitive\n"
                     "package pkg;\n"
                     "endpackage\n"
                     "config cfg;\n"
                     "  design mb;\n"
                     "endconfig\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({a, b}, h.unit));

  EXPECT_NE(h.libs.CellInLibrary("alphaLib", "iface"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("alphaLib", "prog"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("alphaLib", "prim"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("alphaLib", "pkg"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("alphaLib", "cfg"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("betaLib", "iface"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("betaLib", "prog"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("betaLib", "prim"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("betaLib", "pkg"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("betaLib", "cfg"), nullptr);
}

TEST(SinglePassPrecompile, DescriptionNoLibraryDeclarationClaimsStillCompiles) {
  // Being named on the command line is what puts a description into the
  // design; being claimed by a library declaration only decides which library
  // its cells land in. A description that matches no declaration is mapped
  // into the default library rather than refused.
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib rtl/*.v;\n");
  auto loose = tmp.Write("other/loose.v",
                         "module loose;\n"
                         "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_EQ(h.compiler.CompileSource(loose, h.unit), CompileOutcome::kCompiled);

  // The two lookups are what carry the claim. A tag read off the declaration
  // would not: the parser already defaults an untagged cell to the same
  // library name, so that value comes out right whether the description was
  // mapped or not.
  EXPECT_NE(h.libs.CellInLibrary("work", "loose"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("rtlLib", "loose"), nullptr);
  ASSERT_EQ(h.unit.modules.size(), 1u);
  EXPECT_EQ(h.unit.modules[0]->name, "loose");
}

// ---------------------------------------------------------------------------
// Claim: all of the source descriptions shall be provided on the command line,
// and only those descriptions can be used to bind the design.
// ---------------------------------------------------------------------------

TEST(SinglePassPrecompile, DescriptionLeftOffTheCommandLineIsNotRead) {
  // Both files sit in the same directory and are claimed by the same library
  // declaration, so the only thing keeping one of them out of the design is
  // its absence from the command line.
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto named = tmp.Write("src/named.v",
                         "module named;\n"
                         "endmodule\n");
  tmp.Write("src/unnamed.v",
            "module unnamed;\n"
            "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({named}, h.unit));

  EXPECT_NE(h.libs.CellInLibrary("rtlLib", "named"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("rtlLib", "unnamed"), nullptr);
  ASSERT_EQ(h.unit.modules.size(), 1u);
  EXPECT_EQ(h.unit.modules[0]->name, "named");
}

TEST(SinglePassPrecompile, UnreadableDescriptionFailsRatherThanBeingIgnored) {
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto absent = tmp.dir / "src" / "absent.v";

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  EXPECT_EQ(h.compiler.CompileSource(absent, h.unit), CompileOutcome::kFailed);
  EXPECT_TRUE(h.diag.HasErrors());
}

TEST(SinglePassPrecompile, UnparseableDescriptionContributesNoCell) {
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto bad = tmp.Write("src/bad.v",
                       "module bad;\n"
                       "  this is not legal SystemVerilog\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  EXPECT_EQ(h.compiler.CompileSource(bad, h.unit), CompileOutcome::kFailed);
  EXPECT_EQ(h.libs.CellInLibrary("rtlLib", "bad"), nullptr);
  EXPECT_TRUE(h.unit.modules.empty());
}

TEST(SinglePassPrecompile, DirectoryNamedInPlaceOfADescriptionIsRejected) {
  // Something that is not a file at all can still be named on a command line.
  // A directory opens without error on some platforms and then reads as no
  // bytes, which would let it pass for a description that declares no cells
  // and leave the run looking as though the command line had been honoured.
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  tmp.Write("src/real.v",
            "module real_cell;\n"
            "endmodule\n");
  auto dir = tmp.dir / "src";

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  EXPECT_EQ(h.compiler.CompileSource(dir, h.unit), CompileOutcome::kFailed);
  EXPECT_TRUE(h.diag.HasErrors());
  EXPECT_TRUE(h.unit.modules.empty());
}

TEST(SinglePassPrecompile, DescriptionNamedTwiceContributesItsCellsOnce) {
  // Two option files listing a common source put that source on the command
  // line twice, and it is still one description. Compiling it a second time
  // would leave the unit the design binds in holding two declarations of every
  // cell it declares -- a duplicate the user's sources never contained.
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto src = tmp.Write("src/cell.v",
                       "module cell;\n"
                       "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({src, src}, h.unit));

  ASSERT_EQ(h.unit.modules.size(), 1u);
  EXPECT_EQ(h.unit.modules[0]->name, "cell");
  EXPECT_NE(h.libs.CellInLibrary("rtlLib", "cell"), nullptr);
}

TEST(SinglePassPrecompile, DescriptionClaimedByTwoLibrariesHasNowhereToGo) {
  // A description no single library owns cannot be mapped into one, so the
  // precompile reports it rather than picking a library arbitrarily.
  ScratchDir tmp;
  tmp.Write("lib.map",
            "library alphaLib src/cell.v;\n"
            "library betaLib src/cell.v;\n");
  auto src = tmp.Write("src/cell.v",
                       "module cell;\n"
                       "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  EXPECT_EQ(h.compiler.CompileSource(src, h.unit), CompileOutcome::kFailed);
  EXPECT_EQ(h.libs.CellInLibrary("alphaLib", "cell"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("betaLib", "cell"), nullptr);
}

TEST(SinglePassPrecompile, OneUnusableDescriptionDoesNotHideTheOthers) {
  // The whole command line is attempted, so a run names every description it
  // could not use instead of stopping at the first.
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto absent = tmp.dir / "src" / "absent.v";
  auto good = tmp.Write("src/good.v",
                        "module good;\n"
                        "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  EXPECT_FALSE(h.compiler.CompileCommandLine({absent, good}, h.unit));
  EXPECT_NE(h.libs.CellInLibrary("rtlLib", "good"), nullptr);
}

// ---------------------------------------------------------------------------
// Claim: the tool can check whether a cell is already in the library and, if
// its source description has not changed since it was compiled, skip
// recompiling it.
// ---------------------------------------------------------------------------

TEST(SinglePassPrecompile, SkippedDescriptionStillSuppliesItsCells) {
  // Not recompiling a cell is not the same as dropping it: the design still
  // has to be able to bind against what the earlier compile produced.
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto src = tmp.Write("src/cell.v",
                       "module cell;\n"
                       "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_EQ(h.compiler.CompileSource(src, h.unit), CompileOutcome::kCompiled);

  CompilationUnit second;
  ASSERT_EQ(h.compiler.CompileSource(src, second), CompileOutcome::kSkipped);
  ASSERT_EQ(second.modules.size(), 1u);
  EXPECT_EQ(second.modules[0]->name, "cell");
  EXPECT_EQ(second.modules[0]->library, "rtlLib");
}

TEST(SinglePassPrecompile, ChangedDescriptionIsCompiledAgain) {
  // The cell keeps its name across the edit, so only the text of the
  // description can tell the tool that the library's copy is out of date.
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto src = tmp.Write("src/cell.v",
                       "module cell;\n"
                       "  wire before;\n"
                       "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_EQ(h.compiler.CompileSource(src, h.unit), CompileOutcome::kCompiled);
  const LibraryCell* held = h.libs.CellInLibrary("rtlLib", "cell");
  ASSERT_NE(held, nullptr);
  uint32_t first_compile = held->loc.file_id;

  tmp.Write("src/cell.v",
            "module cell;\n"
            "  wire after;\n"
            "endmodule\n");
  CompilationUnit second;
  EXPECT_EQ(h.compiler.CompileSource(src, second), CompileOutcome::kCompiled);

  const LibraryCell* refreshed = h.libs.CellInLibrary("rtlLib", "cell");
  ASSERT_NE(refreshed, nullptr);
  EXPECT_NE(refreshed->loc.file_id, first_compile);
}

TEST(SinglePassPrecompile, UpToDateCheckCanBeTurnedOff) {
  // The standard leaves the check to the tool, so a tool that does not make
  // it compiles every named description afresh and conforms just as well.
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto src = tmp.Write("src/cell.v",
                       "module cell;\n"
                       "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  h.compiler.SetSkipUpToDate(false);
  ASSERT_EQ(h.compiler.CompileSource(src, h.unit), CompileOutcome::kCompiled);

  CompilationUnit second;
  EXPECT_EQ(h.compiler.CompileSource(src, second), CompileOutcome::kCompiled);
}

TEST(SinglePassPrecompile, RecompilingAcrossCommandLinesIsNotADuplicateCell) {
  // Two descriptions of one cell within a single run are a mistake worth
  // warning about; the same cell met again on a later command line is the
  // recompile this use model expects, and warns about nothing.
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto src = tmp.Write("src/cell.v",
                       "module cell;\n"
                       "  wire before;\n"
                       "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({src}, h.unit));
  ASSERT_EQ(h.diag.WarningCount(), 0u);

  tmp.Write("src/cell.v",
            "module cell;\n"
            "  wire after;\n"
            "endmodule\n");
  CompilationUnit second;
  ASSERT_TRUE(h.compiler.CompileCommandLine({src}, second));
  EXPECT_EQ(h.diag.WarningCount(), 0u);
}

// A description declaring more than one cell. Up-to-dateness is a claim about
// every cell a description put into a library, and a description holding one
// cell cannot tell that apart from a claim about some cell or the first one:
// at one cell the three coincide. These two use a description of two cells --
// one that stays put and one that is taken away.

TEST(SinglePassPrecompile, MultiCellDescriptionIsSkippedWhileAllCellsHold) {
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto pair = tmp.Write("src/pair.v",
                        "module alpha;\n"
                        "endmodule\n"
                        "module beta;\n"
                        "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_EQ(h.compiler.CompileSource(pair, h.unit), CompileOutcome::kCompiled);
  ASSERT_EQ(h.unit.modules.size(), 2u);

  CompilationUnit again;
  EXPECT_EQ(h.compiler.CompileSource(pair, again), CompileOutcome::kSkipped);
  EXPECT_EQ(again.modules.size(), 2u);
}

TEST(SinglePassPrecompile, MultiCellDescriptionRedoneWhenOneCellIsTaken) {
  // A second description takes over the name of pair.v's second cell while its
  // first is left alone, so answering this needs every cell in the record
  // consulted: a check that stopped at the first would find alpha in place and
  // wrongly call pair.v up to date. Which cell is taken is not itself a
  // distinction the rule draws -- one loop over the record decides them all --
  // so displacing the other cell instead would retread this same path.
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto pair = tmp.Write("src/pair.v",
                        "module alpha;\n"
                        "endmodule\n"
                        "module beta;\n"
                        "endmodule\n");
  auto dup = tmp.Write("src/rival.v",
                       "module beta;\n"
                       "  wire from_rival;\n"
                       "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_EQ(h.compiler.CompileSource(pair, h.unit), CompileOutcome::kCompiled);
  ASSERT_EQ(h.compiler.CompileSource(dup, h.unit), CompileOutcome::kCompiled);

  CompilationUnit again;
  EXPECT_EQ(h.compiler.CompileSource(pair, again), CompileOutcome::kCompiled);
}

}  // namespace
