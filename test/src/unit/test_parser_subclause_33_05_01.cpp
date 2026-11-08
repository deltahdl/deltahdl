#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"
#include "parser/ast_design.h"
#include "parser/library_map.h"
#include "parser/single_pass_compile.h"

using namespace delta;

namespace {

struct CompileHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap libs;
  CompilationUnit unit;
  SinglePassCompiler compiler{libs, mgr, arena, diag};
};

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

  EXPECT_NE(h.libs.CellInLibrary("gateLib", "spare_adder"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("gateLib", "adder"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("rtlLib", "top"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("rtlLib", "spare_adder"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("gateLib", "top"), nullptr);
}

TEST(SinglePassPrecompile, CompiledCellsAccumulateIntoOneCompilationUnit) {
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
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib rtl/*.v;\n");
  auto loose = tmp.Write("other/loose.v",
                         "module loose;\n"
                         "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_EQ(h.compiler.CompileSource(loose, h.unit), CompileOutcome::kCompiled);

  EXPECT_NE(h.libs.CellInLibrary("work", "loose"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("rtlLib", "loose"), nullptr);
  ASSERT_EQ(h.unit.modules.size(), 1u);
  EXPECT_EQ(h.unit.modules[0]->name, "loose");
}

TEST(SinglePassPrecompile, DescriptionLeftOffTheCommandLineIsNotRead) {
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
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "cannot read source description: ", 0, ""));
}

TEST(SinglePassPrecompile, UnparseableDescriptionIsReportedAsASyntaxError) {
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto bad = tmp.Write("src/bad.v",
                       "module bad;\n"
                       "  this is not legal SystemVerilog\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  EXPECT_EQ(h.compiler.CompileSource(bad, h.unit), CompileOutcome::kFailed);
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "unexpected token in module body", 2, "23.2.4"));
  EXPECT_EQ(h.libs.CellInLibrary("rtlLib", "bad"), nullptr);
  EXPECT_TRUE(h.unit.modules.empty());
}

TEST(SinglePassPrecompile, DirectoryNamedInPlaceOfADescriptionIsRejected) {
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  tmp.Write("src/real.v",
            "module real_cell;\n"
            "endmodule\n");
  auto dir = tmp.dir / "src";

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  EXPECT_EQ(h.compiler.CompileSource(dir, h.unit), CompileOutcome::kFailed);
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "cannot read source description: ", 0, ""));
  EXPECT_TRUE(h.unit.modules.empty());
}

TEST(SinglePassPrecompile, DescriptionNamedTwiceContributesItsCellsOnce) {
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
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "source description claimed by more than one "
                            "library (alphaLib, betaLib): " +
                                src.string(),
                            1, "33.3.1.1"));
  EXPECT_EQ(h.libs.CellInLibrary("alphaLib", "one_cell"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("betaLib", "one_cell"), nullptr);
}

TEST(SinglePassPrecompile, OneUnusableDescriptionDoesNotHideTheOthers) {
  ScratchDir tmp;
  tmp.Write("lib.map", "library rtlLib src/*.v;\n");
  auto absent = tmp.dir / "src" / "absent.v";
  auto good = tmp.Write("src/good.v",
                        "module good;\n"
                        "endmodule\n");

  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  EXPECT_FALSE(h.compiler.CompileCommandLine({absent, good}, h.unit));
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "cannot read source description: ", 0, ""));
  EXPECT_NE(h.libs.CellInLibrary("rtlLib", "good"), nullptr);
}

TEST(SinglePassPrecompile, SkippedDescriptionStillSuppliesItsCells) {
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
