#include <gtest/gtest.h>
#include <unistd.h>

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "parser/library_map.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

// §33.3.1.1 governs how a source file name that matches several library-map
// file_path_specs is resolved to a single library, and how a residual match in
// two libraries is an error. The specs it operates on are produced by the
// §33.3.1 library-declaration syntax, so the file-path-resolution tests build a
// real lib.map, parse it through LoadMapFile (which lexes and parses the
// library_text), and then ask which library a source path maps to. This drives
// the rule on input produced the way the LRM produces it rather than on a
// hand-assembled LibraryMap.
struct TempLibMapDir {
  fs::path dir;

  TempLibMapDir() {
    static std::atomic<uint64_t> counter{0};
    auto seq = counter.fetch_add(1);
    dir = fs::temp_directory_path() /
          ("delta_libmap_3311_" + std::to_string(::getpid()) + "_" +
           std::to_string(seq));
    fs::create_directories(dir);
    // The loader canonicalizes the map file's directory when anchoring relative
    // paths; canonicalize here too so the paths we assert on match its view.
    dir = fs::weakly_canonical(dir);
  }

  ~TempLibMapDir() {
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

// Claim A (resolution order): when a file name matches specs of different
// endings, the more specific ending wins — an explicit file name outranks a
// wildcarded file name, which outranks a directory.

TEST(LibraryMapPathResolution, ExplicitFilenameSpecBeatsWildcard) {
  TempLibMapDir tmp;
  auto top = tmp.Write("lib.map",
                       "library wild *.v;\n"
                       "library exact top.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "exact");
}

TEST(LibraryMapPathResolution,
     ExplicitFilenameSpecBeatsWildcardRegardlessOfDeclarationOrder) {
  // Priority comes from the spec's ending, not from declaration order.
  TempLibMapDir tmp;
  auto top = tmp.Write("lib.map",
                       "library exact top.v;\n"
                       "library wild *.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "exact");
}

TEST(LibraryMapPathResolution, WildcardFilenameSpecBeatsDirectorySpec) {
  TempLibMapDir tmp;
  auto top = tmp.Write("lib.map",
                       "library dir sub/;\n"
                       "library wild sub/*.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.v").string()), "wild");
}

TEST(LibraryMapPathResolution, ExplicitFilenameSpecBeatsDirectorySpec) {
  TempLibMapDir tmp;
  auto top = tmp.Write("lib.map",
                       "library dir sub/;\n"
                       "library exact sub/x.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.v").string()), "exact");
}

TEST(LibraryMapPathResolution, AllThreeTiersPresentExplicitWins) {
  // With every ending competing for the same file, the explicit filename tier
  // is selected.
  TempLibMapDir tmp;
  auto top = tmp.Write("lib.map",
                       "library dirLib sub/;\n"
                       "library wildLib sub/*.v;\n"
                       "library exactLib sub/x.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.v").string()), "exactLib");
}

TEST(LibraryMapPathResolution, DirectorySpecStillResolvesWhenSoleMatch) {
  // The lowest-priority tier (a directory spec) still resolves a file when no
  // higher-priority spec matches it.
  TempLibMapDir tmp;
  auto top = tmp.Write("lib.map", "library dirLib sub/;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.v").string()), "dirLib");
}

TEST(LibraryMapPathResolution,
     MultipleSpecsInOneLibraryResolveByPriorityWithoutError) {
  // Two specs of one library matching the same file is never an error; the
  // cross-library ambiguity rule keys on distinct libraries.
  TempLibMapDir tmp;
  auto top = tmp.Write("lib.map", "library only *.v, top.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "only");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "other.v").string()), "only");
}

TEST(LibraryMapPathResolution,
     HierarchicalWildcardSpecIsDirectoryTierBelowWildcardFilename) {
  // A spec ending in the hierarchical wildcard (...) denotes a directory-tier
  // match, distinct from a trailing-slash directory but still the lowest tier:
  // a wildcarded file name outranks it.
  TempLibMapDir tmp;
  auto top = tmp.Write("lib.map",
                       "library hier sub/...;\n"
                       "library wild sub/*.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.v").string()), "wild");
}

// Claim B (cross-library ambiguity is an error): after resolution, if a file
// still matches specs of the same priority tier in two different libraries, the
// result is an error (LibraryForFile yields no library).

TEST(LibraryMapPathResolution, AmbiguousMatchAcrossLibrariesIsErrorAtExplicit) {
  TempLibMapDir tmp;
  auto top = tmp.Write("lib.map",
                       "library a top.v;\n"
                       "library b top.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "");
}

TEST(LibraryMapPathResolution, AmbiguousMatchAcrossLibrariesIsErrorAtWildcard) {
  // A tie is resolved per tier: two directory specs cannot rescue a file that
  // is ambiguous at the winning (wildcard) tier.
  TempLibMapDir tmp;
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
  // Ambiguity at the lowest tier is still an error: two libraries claim the
  // same file solely through directory specs, with no higher-tier spec to break
  // the tie.
  TempLibMapDir tmp;
  auto top = tmp.Write("lib.map",
                       "library dirA sub/;\n"
                       "library dirB sub/;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.v").string()), "");
}

TEST(LibraryMapPathResolution,
     HigherPriorityTierBreaksWhatWouldBeALowerTierTie) {
  // Two libraries both match via a directory spec, but one also matches via a
  // more specific wildcard spec: the higher tier resolves the file uniquely
  // rather than reporting an ambiguity.
  TempLibMapDir tmp;
  auto top = tmp.Write("lib.map",
                       "library dirA sub/;\n"
                       "library dirB sub/;\n"
                       "library wildA sub/*.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.v").string()), "wildA");
}

// Claim D (last cell wins; duplicate module in a single invocation warns). No
// driver in the tree feeds encountered cells to WriteCell, so there is no
// source syntax that produces this input; the rule is confined to the
// library-map stage and is exercised directly.

TEST(LibraryMapCellWrite, DuplicateNamesInDifferentLibrariesCoexist) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  LibraryMap m;
  m.WriteCell("rtlLib", "adder", /*is_module=*/true, SourceLoc{4, 1, 0}, diag);
  m.WriteCell("gateLib", "adder", /*is_module=*/true, SourceLoc{7, 1, 0}, diag);
  EXPECT_NE(m.CellInLibrary("rtlLib", "adder"), nullptr);
  EXPECT_NE(m.CellInLibrary("gateLib", "adder"), nullptr);
  EXPECT_EQ(diag.WarningCount(), 0u);
}

TEST(LibraryMapCellWrite, DuplicateModuleInSameLibrarySameInvocationWarns) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  LibraryMap m;
  m.WriteCell("rtlLib", "top", /*is_module=*/true, SourceLoc{4, 1, 0}, diag);
  EXPECT_EQ(diag.WarningCount(), 0u);
  m.WriteCell("rtlLib", "top", /*is_module=*/true, SourceLoc{9, 1, 0}, diag);
  EXPECT_GT(diag.WarningCount(), 0u);
  // Last cell still wins despite the warning.
  const LibraryCell* cell = m.CellInLibrary("rtlLib", "top");
  ASSERT_NE(cell, nullptr);
  EXPECT_EQ(cell->loc.file_id, 9u);
}

TEST(LibraryMapCellWrite, RecompileAcrossInvocationsDoesNotWarn) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  LibraryMap m;
  m.WriteCell("rtlLib", "top", /*is_module=*/true, SourceLoc{4, 1, 0}, diag);
  m.BeginNewInvocation();
  // Re-encountering the cell in a later invocation is a recompile: last wins,
  // no warning.
  m.WriteCell("rtlLib", "top", /*is_module=*/true, SourceLoc{9, 1, 0}, diag);
  EXPECT_EQ(diag.WarningCount(), 0u);
  const LibraryCell* cell = m.CellInLibrary("rtlLib", "top");
  ASSERT_NE(cell, nullptr);
  EXPECT_EQ(cell->loc.file_id, 9u);
}

TEST(LibraryMapCellWrite, DuplicateNonModuleCellsInSameLibraryDoNotWarn) {
  // The duplicate-definition warning is specific to modules; other cell kinds
  // are overwritten silently with the last writer winning.
  SourceManager mgr;
  DiagEngine diag(mgr);
  LibraryMap m;
  m.WriteCell("rtlLib", "cfg", /*is_module=*/false, SourceLoc{4, 1, 0}, diag);
  m.WriteCell("rtlLib", "cfg", /*is_module=*/false, SourceLoc{9, 1, 0}, diag);
  EXPECT_EQ(diag.WarningCount(), 0u);
  const LibraryCell* cell = m.CellInLibrary("rtlLib", "cfg");
  ASSERT_NE(cell, nullptr);
  EXPECT_EQ(cell->loc.file_id, 9u);
}

TEST(LibraryMapCellWrite, ModuleAndNonModuleOfSameNameDoNotWarn) {
  // A collision only triggers the warning when both cells are modules; a module
  // overwriting a same-named non-module cell does not.
  SourceManager mgr;
  DiagEngine diag(mgr);
  LibraryMap m;
  m.WriteCell("rtlLib", "thing", /*is_module=*/false, SourceLoc{4, 1, 0}, diag);
  m.WriteCell("rtlLib", "thing", /*is_module=*/true, SourceLoc{9, 1, 0}, diag);
  EXPECT_EQ(diag.WarningCount(), 0u);
}

}  // namespace
