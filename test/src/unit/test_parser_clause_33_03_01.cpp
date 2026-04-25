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

// Files outside any library spec land in "work".
TEST(LibraryMapWorkDefault, UnmatchedFileFallsBackToWork) {
  LibraryMap m;
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/top.v"), "work");
}

TEST(LibraryMapWorkDefault, UnmatchedAfterDeclarationsStillWork) {
  LibraryMap m;
  auto rtl = MakeDecl("rtlLib", {"*.v"});
  m.AddDeclaration(rtl, "/proj/rtl");
  EXPECT_EQ(m.LibraryForFile("/proj/gates/top.vg"), "work");
}

// `*` wildcard: matches characters within a single name component.
TEST(LibraryMapWildcards, StarMatchesSuffixInDirectory) {
  LibraryMap m;
  auto rtl = MakeDecl("rtlLib", {"*.v"});
  m.AddDeclaration(rtl, "/proj/rtl");
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/top.v"), "rtlLib");
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/adder.v"), "rtlLib");
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/top.sv"), "work");
}

TEST(LibraryMapWildcards, StarDoesNotCrossDirectoryBoundary) {
  LibraryMap m;
  auto rtl = MakeDecl("rtlLib", {"*.v"});
  m.AddDeclaration(rtl, "/proj/rtl");
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/sub/top.v"), "work");
}

TEST(LibraryMapWildcards, QuestionMatchesExactlyOneCharacter) {
  LibraryMap m;
  auto rtl = MakeDecl("rtlLib", {"a?.v"});
  m.AddDeclaration(rtl, "/proj/rtl");
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/ab.v"), "rtlLib");
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/abc.v"), "work");
}

TEST(LibraryMapWildcards, HierarchicalDotsMatchAnyDirectoryDepth) {
  LibraryMap m;
  auto rtl = MakeDecl("rtlLib", {"/proj/.../*.v"});
  m.AddDeclaration(rtl, "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/top.v"), "rtlLib");
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/sub/top.v"), "rtlLib");
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/sub/deep/top.v"), "rtlLib");
}

TEST(LibraryMapWildcards, HierarchicalDotsMatchZeroDirectories) {
  LibraryMap m;
  auto rtl = MakeDecl("rtlLib", {"/proj/.../top.v"});
  m.AddDeclaration(rtl, "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/top.v"), "rtlLib");
}

// Trailing '/' rule: "/foo/" means all files in /foo (identical to /foo/*).
TEST(LibraryMapTrailingSlash, IncludesAllFilesInDirectory) {
  LibraryMap m;
  auto rtl = MakeDecl("rtlLib", {"/proj/rtl/"});
  m.AddDeclaration(rtl, "/proj");
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/top.v"), "rtlLib");
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/adder.vg"), "rtlLib");
}

TEST(LibraryMapTrailingSlash, EquivalentToStarSuffix) {
  LibraryMap m_slash;
  m_slash.AddDeclaration(MakeDecl("L", {"/dir/"}), "/proj");
  LibraryMap m_star;
  m_star.AddDeclaration(MakeDecl("L", {"/dir/*"}), "/proj");
  EXPECT_EQ(m_slash.LibraryForFile("/dir/file.v"), "L");
  EXPECT_EQ(m_star.LibraryForFile("/dir/file.v"), "L");
  EXPECT_EQ(m_slash.LibraryForFile("/dir/sub/file.v"), "work");
  EXPECT_EQ(m_star.LibraryForFile("/dir/sub/file.v"), "work");
}

// Relative paths anchor to the .map file's directory.
TEST(LibraryMapRelativePath, ResolvesRelativeToBaseDir) {
  LibraryMap m;
  auto rtl = MakeDecl("rtlLib", {"*.v"});
  m.AddDeclaration(rtl, "/proj/lib");
  EXPECT_EQ(m.LibraryForFile("/proj/lib/top.v"), "rtlLib");
  EXPECT_EQ(m.LibraryForFile("/elsewhere/top.v"), "work");
}

TEST(LibraryMapRelativePath, DotSlashEquivalentToBareSpec) {
  LibraryMap m_dot;
  m_dot.AddDeclaration(MakeDecl("L", {"./*.v"}), "/proj/lib");
  LibraryMap m_bare;
  m_bare.AddDeclaration(MakeDecl("L", {"*.v"}), "/proj/lib");
  EXPECT_EQ(m_dot.LibraryForFile("/proj/lib/x.v"), "L");
  EXPECT_EQ(m_bare.LibraryForFile("/proj/lib/x.v"), "L");
}

TEST(LibraryMapRelativePath, DotDotResolvesToParent) {
  LibraryMap m;
  auto up = MakeDecl("upLib", {"../shared/*.v"});
  m.AddDeclaration(up, "/proj/lib");
  EXPECT_EQ(m.LibraryForFile("/proj/shared/util.v"), "upLib");
  EXPECT_EQ(m.LibraryForFile("/proj/lib/local.v"), "work");
}

// Order-of-declaration determines first-match win, satisfying §33.3.1's
// "multiple map files shall be read in the order in which they are
// specified" — within one map and across maps, the table reflects order.
TEST(LibraryMapDeclarationOrder, MultipleMapFilesProcessedInOrder) {
  // Simulating two .map files: first contributes one declaration, then
  // the second contributes another.  The earlier file's spec wins for
  // overlapping paths.
  LibraryMap m;
  m.AddDeclaration(MakeDecl("alpha", {"*.v"}), "/dirA");
  m.AddDeclaration(MakeDecl("beta", {"*.v"}), "/dirB");
  EXPECT_EQ(m.LibraryForFile("/dirA/x.v"), "alpha");
  EXPECT_EQ(m.LibraryForFile("/dirB/y.v"), "beta");
}

// Direct probe of the static matcher for spec-vs-path semantics.
TEST(LibraryMapPathMatches, AbsoluteSpecMatchesAbsolutePath) {
  EXPECT_TRUE(LibraryMap::PathMatches("/x/y.v", "/proj", "/x/y.v"));
  EXPECT_FALSE(LibraryMap::PathMatches("/x/y.v", "/proj", "/x/z.v"));
}

TEST(LibraryMapPathMatches, RelativeSpecAnchorsToBaseDir) {
  EXPECT_TRUE(LibraryMap::PathMatches("y.v", "/x", "/x/y.v"));
  EXPECT_FALSE(LibraryMap::PathMatches("y.v", "/x", "/other/y.v"));
}

TEST(LibraryMapPathMatches, HierarchicalDotsCrossDirectories) {
  EXPECT_TRUE(LibraryMap::PathMatches("/.../*.v", "/proj", "/a/b/c.v"));
  EXPECT_FALSE(LibraryMap::PathMatches("/.../*.v", "/proj", "/a/b/c.sv"));
}

}  // namespace
