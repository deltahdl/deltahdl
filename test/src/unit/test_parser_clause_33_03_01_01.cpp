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

}
