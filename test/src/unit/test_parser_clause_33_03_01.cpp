#include <gtest/gtest.h>
#include <unistd.h>

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>

#include "parser/ast.h"
#include "parser/library_map.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

LibraryDecl MakeDecl(std::string_view name,
                     std::initializer_list<std::string_view> paths) {
  LibraryDecl d;
  d.name = name;
  for (auto p : paths) d.file_paths.push_back(p);
  return d;
}

// Scratch directory for exercising the "read mapping from a predefined file"
// path of LibraryMap::LoadMapFile. Each instance owns a unique directory that
// is removed on destruction.
struct ScratchMapDir {
  fs::path dir;

  ScratchMapDir() {
    static std::atomic<uint64_t> counter{0};
    dir = fs::temp_directory_path() /
          ("delta_lm3301_" + std::to_string(::getpid()) + "_" +
           std::to_string(counter.fetch_add(1)));
    fs::create_directories(dir);
  }

  ~ScratchMapDir() {
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

// §33.3.1 edge: the single-character wildcard stands for exactly one
// character, so a name missing that position does not match (lower bound,
// complementing the "no more than one" case above).
TEST(LibraryMapWildcards, QuestionDoesNotMatchMissingCharacter) {
  LibraryMap m;
  auto rtl = MakeDecl("rtlLib", {"a?.v"});
  m.AddDeclaration(rtl, "/proj/rtl");
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/a.v"), "work");
}

// §33.3.1 edge: the multi-character wildcard matches an empty run as well as a
// non-empty one within a single name component.
TEST(LibraryMapWildcards, StarMatchesEmptySequence) {
  LibraryMap m;
  auto rtl = MakeDecl("rtlLib", {"top*.v"});
  m.AddDeclaration(rtl, "/proj/rtl");
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/top.v"), "rtlLib");
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/topmost.v"), "rtlLib");
}

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

// §33.3.1: the library mapping information is read from a predefined map file
// prior to parsing source files. Exercise the file-reading path itself rather
// than constructing entries directly, so the mapping that drives source-to-
// library assignment is observed to come from the file on disk.
TEST(LibraryMapFileReading, ReadsMappingFromPredefinedFile) {
  ScratchMapDir tmp;
  auto map_file = tmp.Write("lib.map", "library rtlLib *.v;\n");

  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(map_file));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "rtlLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.sv").string()), "work");
}

// §33.3.1: a tool shall accept one or more library map files for an invocation,
// and when several are specified they are read in the order given. Loading two
// independent map files in sequence stands in for two files named at
// invocation; both contribute and their declarations keep the load order.
TEST(LibraryMapFileReading, MultipleMapFilesReadInSpecifiedOrder) {
  ScratchMapDir tmp;
  auto first = tmp.Write("dirA/lib.map", "library alpha *.v;\n");
  auto second = tmp.Write("dirB/lib.map", "library beta *.v;\n");

  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(first));
  ASSERT_TRUE(m.LoadMapFile(second));

  EXPECT_EQ(m.LibraryForFile((tmp.dir / "dirA/x.v").string()), "alpha");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "dirB/y.v").string()), "beta");

  std::vector<std::string_view> order = m.LibraryDeclarationOrder();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "alpha");
  EXPECT_EQ(order[1], "beta");
}

// §33.3.1: reading order follows specification order. The same two map files
// loaded in the opposite sequence yield the opposite declaration order,
// confirming the order is governed by the order the files are read.
TEST(LibraryMapFileReading, DeclarationOrderFollowsLoadOrder) {
  ScratchMapDir tmp;
  auto first = tmp.Write("dirA/lib.map", "library alpha *.v;\n");
  auto second = tmp.Write("dirB/lib.map", "library beta *.v;\n");

  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(second));
  ASSERT_TRUE(m.LoadMapFile(first));

  std::vector<std::string_view> order = m.LibraryDeclarationOrder();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "beta");
  EXPECT_EQ(order[1], "alpha");
}

// §33.3.1 error condition: reading the mapping requires the predefined file to
// exist. When it cannot be opened the read reports failure and surfaces a
// diagnostic rather than silently yielding an empty mapping.
TEST(LibraryMapFileReading, NonexistentMapFileReportsFailure) {
  ScratchMapDir tmp;
  LibraryMap m;
  std::vector<std::string> errors;
  EXPECT_FALSE(m.LoadMapFile(tmp.dir / "absent.map", &errors));
  EXPECT_FALSE(errors.empty());
}

// §33.3.1 error condition: a predefined map file whose contents do not parse as
// valid mapping information causes the read to fail and report the problem.
TEST(LibraryMapFileReading, MalformedMapFileReportsFailure) {
  ScratchMapDir tmp;
  auto bad = tmp.Write("lib.map", "library;\n");
  LibraryMap m;
  std::vector<std::string> errors;
  EXPECT_FALSE(m.LoadMapFile(bad, &errors));
  EXPECT_FALSE(errors.empty());
}

}  // namespace
