#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"
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
  // The report is about the run rather than about a construct somebody wrote,
  // so SinglePassCompiler::CompileSource emits it with SourceLoc::None() and
  // Subclause::None(): line 0 and no subclause are what the emission site
  // passes.
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "cannot read source description: ", 0, ""));
}

TEST(SinglePassPrecompile, UnparseableDescriptionIsReportedAsASyntaxError) {
  // Reading the failure back off the engine is what says the description was
  // rejected for the reason this test wrote it to be rejected for. Every other
  // way a compile can fail -- a path that cannot be read, a description two
  // libraries claim, a library map that will not load -- fails the same way,
  // so the outcome alone leaves the case below satisfied by a run that never
  // reached the source at all.
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto bad = tmp.Write("src/bad.v",
                       "module bad;\n"
                       "  this is not legal SystemVerilog\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  EXPECT_EQ(h.compiler.CompileSource(bad, h.unit), CompileOutcome::kFailed);
  // §23.2.4 owns the module body, so the stray text is reported there rather
  // than under §33.5.1.
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "unexpected token in module body", 2, "23.2.4"));
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
  // The directory is refused by the read, whose report is about the run rather
  // than about a construct: line 0 and no subclause are what the emission site
  // passes.
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "cannot read source description: ", 0, ""));
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
                       "module one_cell;\n"
                       "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({src, src}, h.unit));

  ASSERT_EQ(h.unit.modules.size(), 1u);
  EXPECT_EQ(h.unit.modules[0]->name, "one_cell");
  EXPECT_NE(h.libs.CellInLibrary("rtlLib", "one_cell"), nullptr);
}

TEST(SinglePassPrecompile,
     DescriptionClaimedByTwoLibrariesNamesBothInItsDiagnostic) {
  // A description no single library owns cannot be mapped into one, so the
  // precompile reports it rather than picking a library arbitrarily. What it
  // reports names both claimants, so this case is about the ambiguity rather
  // than about the compile having failed: a description that never parsed, or
  // that could not be read, fails the compile and leaves both libraries empty
  // in exactly the same way, so a case satisfied by that establishes nothing
  // about §33.5.1.
  ScratchDir tmp;
  tmp.Write("lib.map",
            "library alphaLib src/cell.v;\n"
            "library betaLib src/cell.v;\n");
  auto src = tmp.Write("src/cell.v",
                       "module one_cell;\n"
                       "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  EXPECT_EQ(h.compiler.CompileSource(src, h.unit), CompileOutcome::kFailed);
  ASSERT_EQ(h.diag.Diagnostics().size(), 1u);
  // §33.3.1.1 makes the double claim an error, so that is the subclause the
  // report names; the position is the first claiming declaration, on line 1 of
  // the map file.
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "source description claimed by more than one "
                            "library (alphaLib, betaLib): " +
                                src.string(),
                            1, "33.3.1.1"));
  EXPECT_EQ(h.libs.CellInLibrary("alphaLib", "one_cell"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("betaLib", "one_cell"), nullptr);
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
  // The run names the description it could not read, and that report is about
  // the run rather than about a construct: line 0 and no subclause are what
  // the emission site passes.
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "cannot read source description: ", 0, ""));
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
                       "module one_cell;\n"
                       "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_EQ(h.compiler.CompileSource(src, h.unit), CompileOutcome::kCompiled);

  CompilationUnit second;
  ASSERT_EQ(h.compiler.CompileSource(src, second), CompileOutcome::kSkipped);
  ASSERT_EQ(second.modules.size(), 1u);
  EXPECT_EQ(second.modules[0]->name, "one_cell");
  EXPECT_EQ(second.modules[0]->library, "rtlLib");
}

TEST(SinglePassPrecompile, ChangedDescriptionIsCompiledAgain) {
  // The cell keeps its name across the edit, so only the text of the
  // description can tell the tool that the library's copy is out of date.
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto src = tmp.Write("src/cell.v",
                       "module one_cell;\n"
                       "  wire earlier;\n"
                       "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_EQ(h.compiler.CompileSource(src, h.unit), CompileOutcome::kCompiled);
  const LibraryCell* held = h.libs.CellInLibrary("rtlLib", "one_cell");
  ASSERT_NE(held, nullptr);
  uint32_t first_compile = held->loc.file_id;

  tmp.Write("src/cell.v",
            "module one_cell;\n"
            "  wire later;\n"
            "endmodule\n");
  CompilationUnit second;
  EXPECT_EQ(h.compiler.CompileSource(src, second), CompileOutcome::kCompiled);

  const LibraryCell* refreshed = h.libs.CellInLibrary("rtlLib", "one_cell");
  ASSERT_NE(refreshed, nullptr);
  EXPECT_NE(refreshed->loc.file_id, first_compile);
}

TEST(SinglePassPrecompile, UpToDateCheckCanBeTurnedOff) {
  // The standard leaves the check to the tool, so a tool that does not make
  // it compiles every named description afresh and conforms just as well.
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto src = tmp.Write("src/cell.v",
                       "module one_cell;\n"
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
                       "module one_cell;\n"
                       "  wire earlier;\n"
                       "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({src}, h.unit));
  ASSERT_EQ(h.diag.WarningCount(), 0u);

  tmp.Write("src/cell.v",
            "module one_cell;\n"
            "  wire later;\n"
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

// ---------------------------------------------------------------------------
// Claim: every design element a description declares is a cell of the library
// that description maps to, and §3.2 says which kinds those are.
// ---------------------------------------------------------------------------

// §33.2.1: "A library is a named collection of cells. A cell is a design
// element (see 3.2), such as a module, primitive, interface, program, package,
// or configuration." The six it names are introduced by "such as" and §3.2 is
// what the definition defers to, which names seven: "A design element is a
// SystemVerilog module (see Clause 23), program (see Clause 24), interface (see
// Clause 25), checker (see Clause 17), package (see Clause 26), primitive (see
// Clause 28) or configuration (see Clause 33)." The checker is the kind reading
// §33.2.1's examples as the whole set leaves out, so it gets a case of its own.
TEST(SinglePassPrecompile, CheckerIsWrittenIntoTheLibraryItsDescriptionMapsTo) {
  ScratchDir tmp;
  tmp.Write("lib.map", "library chkLib checked/*.sv;\n");
  auto src = tmp.Write("checked/chk.sv",
                       "checker watchdog;\n"
                       "endchecker\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({src}, h.unit));
  EXPECT_NE(h.libs.CellInLibrary("chkLib", "watchdog"), nullptr);
}

// One description declaring all seven kinds §3.2 names, so the next kind left
// out of the write goes red here rather than waiting for a case of its own.
TEST(SinglePassPrecompile, EveryDesignElementKindIsWrittenIntoTheLibrary) {
  ScratchDir tmp;
  tmp.Write("lib.map", "library everyLib every/*.sv;\n");
  auto src = tmp.Write("every/all_kinds.sv",
                       "module top_cell;\n"
                       "endmodule\n"
                       "program test_prog;\n"
                       "endprogram\n"
                       "interface bus_if;\n"
                       "endinterface\n"
                       "checker watchdog;\n"
                       "endchecker\n"
                       "package util_pkg;\n"
                       "endpackage\n"
                       "primitive inv_prim(output o, input a);\n"
                       "  table\n"
                       "    0 : 1;\n"
                       "    1 : 0;\n"
                       "  endtable\n"
                       "endprimitive\n"
                       "config cfg_all;\n"
                       "  design top_cell;\n"
                       "endconfig\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({src}, h.unit));
  EXPECT_NE(h.libs.CellInLibrary("everyLib", "top_cell"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("everyLib", "test_prog"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("everyLib", "bus_if"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("everyLib", "watchdog"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("everyLib", "util_pkg"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("everyLib", "inv_prim"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("everyLib", "cfg_all"), nullptr);
}

// A description whose cells are never written records nothing for
// SinglePassCompiler::CellsStillHeldInLibraries to consult, and that function
// answers true over an empty record, so the description is called up to date
// without anything about it having been examined. A second description takes
// the checker's name away here, which is the displacement
// MultiCellDescriptionRedoneWhenOneCellIsTaken above builds on for modules: it
// is what makes the answer kCompiled rather than kSkipped, and it can only do
// so once the checker is a cell the record holds.
TEST(SinglePassPrecompile,
     CheckerOnlyDescriptionIsRedoneWhenItsCheckerIsTaken) {
  ScratchDir tmp;
  tmp.Write("lib.map", "library chkLib checked/*.sv;\n");
  auto first = tmp.Write("checked/first.sv",
                         "checker watchdog;\n"
                         "endchecker\n");
  auto rival = tmp.Write("checked/rival.sv",
                         "checker watchdog;\n"
                         "  logic flag = 0;\n"
                         "endchecker\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_EQ(h.compiler.CompileSource(first, h.unit), CompileOutcome::kCompiled);
  ASSERT_EQ(h.compiler.CompileSource(rival, h.unit), CompileOutcome::kCompiled);

  CompilationUnit again;
  EXPECT_EQ(h.compiler.CompileSource(first, again), CompileOutcome::kCompiled);
}

}  // namespace
