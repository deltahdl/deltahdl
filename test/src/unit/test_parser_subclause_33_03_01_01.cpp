#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <initializer_list>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"
#include "parser/ast_design.h"
#include "parser/library_map.h"
#include "parser/single_pass_compile.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

TEST(LibraryMapPathResolution, ExplicitFilenameSpecBeatsWildcard) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map",
                       "library wild *.v;\n"
                       "library exact top.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "exact");
}

TEST(LibraryMapPathResolution,
     ExplicitFilenameSpecBeatsWildcardRegardlessOfDeclarationOrder) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map",
                       "library exact top.v;\n"
                       "library wild *.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "exact");
}

TEST(LibraryMapPathResolution, WildcardFilenameSpecBeatsDirectorySpec) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map",
                       "library dir sub/;\n"
                       "library wild sub/*.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.v").string()), "wild");
}

TEST(LibraryMapPathResolution, ExplicitFilenameSpecBeatsDirectorySpec) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map",
                       "library dir sub/;\n"
                       "library exact sub/x.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.v").string()), "exact");
}

TEST(LibraryMapPathResolution, AllThreeTiersPresentExplicitWins) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map",
                       "library dirLib sub/;\n"
                       "library wildLib sub/*.v;\n"
                       "library exactLib sub/x.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.v").string()), "exactLib");
}

TEST(LibraryMapPathResolution, DirectorySpecStillResolvesWhenSoleMatch) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map", "library dirLib sub/;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.v").string()), "dirLib");
}

TEST(LibraryMapPathResolution,
     MultipleSpecsInOneLibraryResolveByPriorityWithoutError) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map", "library only *.v, top.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "only");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "other.v").string()), "only");
}

TEST(LibraryMapPathResolution,
     TwoSpecsOfOneTierInOneLibraryNameThatLibraryOnce) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map", "library only *.v, t*.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibrariesForFile((tmp.dir / "top.v").string()).size(), 1u);
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "only");
}

TEST(LibraryMapPathResolution,
     HierarchicalWildcardSpecIsDirectoryTierBelowWildcardFilename) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map",
                       "library hier sub/...;\n"
                       "library wild sub/*.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.v").string()), "wild");
}

TEST(LibraryMapPathResolution, AmbiguousMatchAcrossLibrariesIsErrorAtExplicit) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map",
                       "library a top.v;\n"
                       "library b top.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "");
}

TEST(LibraryMapPathResolution, AmbiguousMatchAcrossLibrariesIsErrorAtWildcard) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map",
                       "library dir sub/;\n"
                       "library wildA sub/*.v;\n"
                       "library wildB sub/*.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.v").string()), "");
}

TEST(LibraryMapPathResolution,
     AmbiguousMatchAcrossLibrariesIsErrorAtDirectory) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map",
                       "library dirA sub/;\n"
                       "library dirB sub/;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.v").string()), "");
}

TEST(LibraryMapPathResolution,
     HigherPriorityTierBreaksWhatWouldBeALowerTierTie) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map",
                       "library dirA sub/;\n"
                       "library dirB sub/;\n"
                       "library wildA sub/*.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.v").string()), "wildA");
}

void ExpectClaimByTwoLibrariesReported(ScratchDir& tmp,
                                       std::initializer_list<const char*> maps,
                                       uint32_t line) {
  auto src = tmp.Write("sub/cell.v",
                       "module one_cell;\n"
                       "endmodule\n");
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap libs;
  CompilationUnit unit;
  SinglePassCompiler compiler{libs, mgr, arena, diag};
  for (const char* map : maps) {
    ASSERT_TRUE(libs.LoadMapFile(tmp.dir / map));
  }
  EXPECT_EQ(compiler.CompileSource(src, unit), CompileOutcome::kFailed);
  EXPECT_TRUE(ReportedError(diag.Diagnostics(),
                            "claimed by more than one library", line,
                            "33.3.1.1"));
}

TEST(LibraryMapAmbiguityReport, ClaimByTwoLibrariesStandsAtFirstDeclaration) {
  ScratchDir tmp;
  tmp.Write("lib.map",
            "// Two declarations claim sub/cell.v as specifically as each\n"
            "// other, so no library holds it and the compile stops.\n"
            "//\n"
            "library alphaLib sub/cell.v;\n"
            "library betaLib sub/cell.v;\n");
  ExpectClaimByTwoLibrariesReported(tmp, {"lib.map"}, 4);
}

TEST(LibraryMapAmbiguityReport, TieOfWildcardedFileNamesIsReported) {
  ScratchDir tmp;
  tmp.Write("lib.map",
            "library otherLib lib/*.v;\n"
            "library wildA sub/*.v;\n"
            "library wildB sub/*.v;\n");
  ExpectClaimByTwoLibrariesReported(tmp, {"lib.map"}, 2);
}

TEST(LibraryMapAmbiguityReport, TieOfDirectoriesIsReported) {
  ScratchDir tmp;
  tmp.Write("lib.map",
            "library otherLib lib/;\n"
            "library dirA sub/;\n"
            "library dirB sub/;\n");
  ExpectClaimByTwoLibrariesReported(tmp, {"lib.map"}, 2);
}

TEST(LibraryMapAmbiguityReport, TieAcrossTwoMapFilesOfOneRunIsReported) {
  ScratchDir tmp;
  tmp.Write("one.map", "library alphaLib sub/*.v;\n");
  tmp.Write("two.map",
            "\n"
            "\n"
            "library betaLib sub/*.v;\n");
  ExpectClaimByTwoLibrariesReported(tmp, {"one.map", "two.map"}, 1);
}

TEST(LibraryMapAmbiguityReport, TieWithAnIncludedMapFileIsReported) {
  ScratchDir tmp;
  tmp.Write("inner.map",
            "\n"
            "\n"
            "library alphaLib sub/*.v;\n");
  tmp.Write("outer.map",
            "include inner.map;\n"
            "library betaLib sub/*.v;\n");
  ExpectClaimByTwoLibrariesReported(tmp, {"outer.map"}, 3);
}

TEST(LibraryMapAmbiguityReport, FileNoDeclarationClaimsHasNoDeclarationToName) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map", "library alphaLib src/*.v;\n");
  SourceManager mgr;
  LibraryMap m;
  m.ResolvePositionsAgainst(mgr);
  ASSERT_TRUE(m.LoadMapFile(top));
  ASSERT_TRUE(m.FirstDeclarationClaiming((tmp.dir / "src" / "cell.v").string())
                  .IsValid());
  EXPECT_FALSE(
      m.FirstDeclarationClaiming((tmp.dir / "other" / "cell.sv").string())
          .IsValid());
}

TEST(LibraryMapCellWrite, DuplicateNamesInDifferentLibrariesCoexist) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  LibraryMap m;
  m.WriteCell("rtlLib", "adder", true, SourceLoc{4, 1, 0}, diag);
  m.WriteCell("gateLib", "adder", true, SourceLoc{7, 1, 0}, diag);
  EXPECT_NE(m.CellInLibrary("rtlLib", "adder"), nullptr);
  EXPECT_NE(m.CellInLibrary("gateLib", "adder"), nullptr);
  EXPECT_EQ(diag.WarningCount(), 0u);
}

TEST(LibraryMapCellWrite, DuplicateModuleInSameLibrarySameInvocationWarns) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  LibraryMap m;
  m.WriteCell("rtlLib", "top", true, SourceLoc{4, 1, 0}, diag);
  EXPECT_EQ(diag.WarningCount(), 0u);
  m.WriteCell("rtlLib", "top", true, SourceLoc{9, 7, 0}, diag);
  EXPECT_TRUE(ReportedWarning(diag.Diagnostics(),
                              "module 'top' is written to library 'rtlLib' "
                              "more than once in this invocation",
                              7, "33.3.1.1"));
  const LibraryCell* cell = m.CellInLibrary("rtlLib", "top");
  ASSERT_NE(cell, nullptr);
  EXPECT_EQ(cell->loc.file_id, 9u);
}

TEST(LibraryMapCellWrite, RecompileAcrossInvocationsDoesNotWarn) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  LibraryMap m;
  m.WriteCell("rtlLib", "top", true, SourceLoc{4, 1, 0}, diag);
  m.BeginNewInvocation();
  m.WriteCell("rtlLib", "top", true, SourceLoc{9, 1, 0}, diag);
  EXPECT_EQ(diag.WarningCount(), 0u);
  const LibraryCell* cell = m.CellInLibrary("rtlLib", "top");
  ASSERT_NE(cell, nullptr);
  EXPECT_EQ(cell->loc.file_id, 9u);
}

TEST(LibraryMapCellWrite, DuplicateNonModuleCellsInSameLibraryDoNotWarn) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  LibraryMap m;
  m.WriteCell("rtlLib", "cfg", false, SourceLoc{4, 1, 0}, diag);
  m.WriteCell("rtlLib", "cfg", false, SourceLoc{9, 1, 0}, diag);
  EXPECT_EQ(diag.WarningCount(), 0u);
  const LibraryCell* cell = m.CellInLibrary("rtlLib", "cfg");
  ASSERT_NE(cell, nullptr);
  EXPECT_EQ(cell->loc.file_id, 9u);
}

TEST(LibraryMapCellWrite, ModuleAndNonModuleOfSameNameDoNotWarn) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  LibraryMap m;
  m.WriteCell("rtlLib", "thing", false, SourceLoc{4, 1, 0}, diag);
  m.WriteCell("rtlLib", "thing", true, SourceLoc{9, 1, 0}, diag);
  EXPECT_EQ(diag.WarningCount(), 0u);
}

}  // namespace
