#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "parser/library_map.h"

using namespace delta;

namespace {

LibraryDecl MakeDecl(std::string_view name,
                     std::initializer_list<std::string_view> paths) {
  LibraryDecl d;
  d.name = name;
  for (auto p : paths) d.file_paths.push_back(p);
  return d;
}

TEST(LibraryMapPathResolution, AmbiguousMatchAcrossLibrariesIsError) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("first", {"*.v"}), "/proj");
  m.AddDeclaration(MakeDecl("second", {"*.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/file.v"), "");
}

TEST(LibraryMapPathResolution, ExplicitFilenameSpecBeatsWildcard) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("wild", {"*.v"}), "/proj");
  m.AddDeclaration(MakeDecl("exact", {"top.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/top.v"), "exact");
}

TEST(LibraryMapPathResolution,
     ExplicitFilenameSpecBeatsWildcardRegardlessOfOrder) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("exact", {"top.v"}), "/proj");
  m.AddDeclaration(MakeDecl("wild", {"*.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/top.v"), "exact");
}

TEST(LibraryMapPathResolution, WildcardFilenameSpecBeatsDirectorySpec) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("dir", {"sub/"}), "/proj");
  m.AddDeclaration(MakeDecl("wild", {"sub/*.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/sub/x.v"), "wild");
}

TEST(LibraryMapPathResolution, ExplicitFilenameSpecBeatsDirectorySpec) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("dir", {"sub/"}), "/proj");
  m.AddDeclaration(MakeDecl("exact", {"sub/x.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/sub/x.v"), "exact");
}

TEST(LibraryMapPathResolution,
     SameLibraryMultipleSpecsResolveByPriorityWithoutError) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("only", {"*.v", "top.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/top.v"), "only");
  EXPECT_EQ(m.LibraryForFile("/proj/other.v"), "only");
}

TEST(LibraryMapPathResolution, HigherPrioritySpecAcrossLibrariesPicksThatLib) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("dirLib", {"sub/"}), "/proj");
  m.AddDeclaration(MakeDecl("wildLib", {"sub/*.v"}), "/proj");
  m.AddDeclaration(MakeDecl("exactLib", {"sub/x.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/sub/x.v"), "exactLib");
}

TEST(LibraryMapPathResolution, AmbiguityAtPriorityTierIsError) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("dir", {"sub/"}), "/proj");
  m.AddDeclaration(MakeDecl("wildA", {"sub/*.v"}), "/proj");
  m.AddDeclaration(MakeDecl("wildB", {"sub/*.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/sub/x.v"), "");
}

TEST(LibraryMapPathResolution, DirectorySpecMatchesWhenSoleSpec) {
  // The lowest-priority tier (a directory spec) still resolves a file when no
  // higher-priority spec matches it.
  LibraryMap m;
  m.AddDeclaration(MakeDecl("dirLib", {"sub/"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/sub/x.v"), "dirLib");
}

TEST(LibraryMapPathResolution, AmbiguityAtExplicitTierIsError) {
  // Two libraries claiming the same explicit filename are ambiguous even at the
  // highest-priority tier.
  LibraryMap m;
  m.AddDeclaration(MakeDecl("a", {"top.v"}), "/proj");
  m.AddDeclaration(MakeDecl("b", {"top.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/top.v"), "");
}

TEST(LibraryMapCellWrite, LastCellWithSameNameWinsInLibrary) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  LibraryMap m;
  m.WriteCell("rtlLib", "adder", /*is_module=*/false, SourceLoc{4, 1, 0}, diag);
  m.WriteCell("rtlLib", "adder", /*is_module=*/false, SourceLoc{9, 2, 0}, diag);
  const LibraryCell* cell = m.CellInLibrary("rtlLib", "adder");
  ASSERT_NE(cell, nullptr);
  // The most recently written cell replaces the earlier one.
  EXPECT_EQ(cell->loc.file_id, 9u);
}

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
