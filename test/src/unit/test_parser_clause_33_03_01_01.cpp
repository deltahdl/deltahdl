#include <gtest/gtest.h>

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

// §33.3.1.1: when a path is matched by specs in multiple library
// definitions at the same priority level (after spec-type priority is
// applied), the resolver shall not silently choose one — the result is
// surfaced as an empty library name so the driver can report the error.
TEST(LibraryMapPathResolution, AmbiguousMatchAcrossLibrariesIsError) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("first", {"*.v"}), "/proj");
  m.AddDeclaration(MakeDecl("second", {"*.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/file.v"), "");
}

// §33.3.1.1 priority: an explicit-filename spec wins over a wildcarded
// filename even when the wildcarded entry was declared first.
TEST(LibraryMapPathResolution, ExplicitFilenameSpecBeatsWildcard) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("wild", {"*.v"}), "/proj");
  m.AddDeclaration(MakeDecl("exact", {"top.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/top.v"), "exact");
}

// Same priority outcome regardless of declaration order — confirms the
// resolver classifies entries by spec type, not by index.
TEST(LibraryMapPathResolution,
     ExplicitFilenameSpecBeatsWildcardRegardlessOfOrder) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("exact", {"top.v"}), "/proj");
  m.AddDeclaration(MakeDecl("wild", {"*.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/top.v"), "exact");
}

// §33.3.1.1 priority: a wildcarded-filename spec wins over a directory
// spec.
TEST(LibraryMapPathResolution, WildcardFilenameSpecBeatsDirectorySpec) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("dir", {"sub/"}), "/proj");
  m.AddDeclaration(MakeDecl("wild", {"sub/*.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/sub/x.v"), "wild");
}

// §33.3.1.1 priority: an explicit-filename spec wins over a directory
// spec — covers the highest-vs-lowest priority pair.
TEST(LibraryMapPathResolution, ExplicitFilenameSpecBeatsDirectorySpec) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("dir", {"sub/"}), "/proj");
  m.AddDeclaration(MakeDecl("exact", {"sub/x.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/sub/x.v"), "exact");
}

// Two specs in the same library, different priorities — same-library
// matches do not trigger the cross-library error of §33.3.1.1.
TEST(LibraryMapPathResolution,
     SameLibraryMultipleSpecsResolveByPriorityWithoutError) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("only", {"*.v", "top.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/top.v"), "only");
  EXPECT_EQ(m.LibraryForFile("/proj/other.v"), "only");
}

// Two libraries each contribute a different priority spec — the
// higher-priority library wins, no ambiguity.
TEST(LibraryMapPathResolution, HigherPrioritySpecAcrossLibrariesPicksThatLib) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("dirLib", {"sub/"}), "/proj");
  m.AddDeclaration(MakeDecl("wildLib", {"sub/*.v"}), "/proj");
  m.AddDeclaration(MakeDecl("exactLib", {"sub/x.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/sub/x.v"), "exactLib");
}

// Ambiguity at the wildcarded-filename tier still errors even when a
// lower-priority spec also matches — priority is applied first.
TEST(LibraryMapPathResolution, AmbiguityAtPriorityTierIsError) {
  LibraryMap m;
  m.AddDeclaration(MakeDecl("dir", {"sub/"}), "/proj");
  m.AddDeclaration(MakeDecl("wildA", {"sub/*.v"}), "/proj");
  m.AddDeclaration(MakeDecl("wildB", {"sub/*.v"}), "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/sub/x.v"), "");
}

}  // namespace
