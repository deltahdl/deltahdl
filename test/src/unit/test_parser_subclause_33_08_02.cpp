#include <gtest/gtest.h>

#include <array>
#include <filesystem>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "fixture_scratch_dir.h"
#include "fixture_tagged_file.h"
#include "parser/library_map.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

constexpr std::array<std::string_view, 4> kTreePaths = {
    "lib1/rtl/a.v", "lib2/gates/a.v", "lib1/rtl/b.v", "lib2/gates/b.v"};

constexpr const char* kCellA = "module a;\nendmodule\n";
constexpr const char* kCellB = "module b;\nendmodule\n";

void WriteTree(ScratchDir& tmp) {
  tmp.Write("lib1/rtl/a.v", kCellA);
  tmp.Write("lib2/gates/a.v", kCellA);
  tmp.Write("lib1/rtl/b.v", kCellB);
  tmp.Write("lib2/gates/b.v", kCellB);
}

struct ExampleMap {
  LibraryMap map;
  bool loaded = false;

  ExampleMap(ScratchDir& tmp, const std::string& map_rel,
             const std::string& spec) {
    auto map_file = tmp.Write(map_rel, "library exLib " + spec + ";\n");
    loaded = map.LoadMapFile(map_file);
  }
};

struct SharedFileMap {
  LibraryMap map;
  bool loaded = false;

  SharedFileMap(ScratchDir& tmp, const std::string& map_rel,
                const std::string& first, const std::string& second) {
    std::string text = "library firstLib " + first + ";\n";
    text += "library secondLib " + second + ";\n";
    loaded = map.LoadMapFile(tmp.Write(map_rel, text));
  }
};

std::string Reached(const ExampleMap& m, const ScratchDir& tmp) {
  std::string out;
  for (auto rel : kTreePaths) {
    auto path = (tmp.dir / std::string(rel)).string();
    if (m.map.LibraryForFile(path) != "exLib") continue;
    if (!out.empty()) out += ' ';
    out.append(rel);
  }
  return out;
}

std::string Rooted(const ScratchDir& tmp, const std::string& tail) {
  return tmp.dir.string() + "/" + tail;
}

TEST(FilePathSpecExampleResolution,
     WildcardedDirectoryNameDoesNotSpanTwoDirectories) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib.map", Rooted(tmp, "lib*/a.v"));
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "");
}

TEST(FilePathSpecExampleResolution,
     RootedSpecReachesBothDescriptionsWhereverItIsDeclared) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib1/lib.map", Rooted(tmp, "lib*/*/a.v"));
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib1/rtl/a.v lib2/gates/a.v");
}

TEST(FilePathSpecExampleResolution,
     HierarchicalWildcardOpeningASpecReachesEveryDepth) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib.map", ".../a.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib1/rtl/a.v lib2/gates/a.v");
}

TEST(FilePathSpecExampleResolution,
     HierarchicalWildcardIsAnchoredAtTheDirectoryResolvedFrom) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib2/lib.map", ".../a.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib2/gates/a.v");
}

TEST(FilePathSpecExampleResolution,
     HierarchicalWildcardDoesNotReachOutsideItsRootedPrefix) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib.map", Rooted(tmp, "lib1/.../b.v"));
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib1/rtl/b.v");
}

TEST(FilePathSpecExampleResolution,
     RootedHierarchicalWildcardReachesEveryDepthWhereverDeclared) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib2/gates/lib.map", Rooted(tmp, ".../b.v"));
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib1/rtl/b.v lib2/gates/b.v");
}

TEST(FilePathSpecExampleResolution,
     NamedDirectoryAfterHierarchicalWildcardSelectsThatDirectory) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib.map", ".../rtl/*.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib1/rtl/a.v lib1/rtl/b.v");
}

TEST(FilePathSpecExampleResolution,
     WildcardedFileNameAfterHierarchicalWildcardStaysInOneDirectory) {
  ScratchDir tmp;
  WriteTree(tmp);
  auto deeper = tmp.Write("lib1/rtl/sub/c.v", "module c;\nendmodule\n");
  ExampleMap m(tmp, "lib.map", ".../rtl/*.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.map.LibraryForFile(deeper.string()), "work");
}

TEST(FilePathSpecExampleResolution, ParentStepReachesIntoASiblingDirectory) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib1/lib.map", "../lib2/gates/*.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib2/gates/a.v lib2/gates/b.v");
}

TEST(FilePathSpecExampleResolution,
     SpecWithoutTheParentStepStaysBelowItsOwnDirectory) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib1/lib.map", "lib2/gates/*.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "");
}

TEST(FilePathSpecExampleResolution,
     SingleCharacterWildcardReachesEveryOneCharacterName) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib1/lib.map", "./rtl/?.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib1/rtl/a.v lib1/rtl/b.v");
}

TEST(FilePathSpecExampleResolution,
     SingleCharacterWildcardDoesNotReachALongerName) {
  ScratchDir tmp;
  WriteTree(tmp);
  auto longer = tmp.Write("lib1/rtl/ab.v", "module ab;\nendmodule\n");
  ExampleMap m(tmp, "lib1/lib.map", "./rtl/?.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.map.LibraryForFile(longer.string()), "work");
}

TEST(FilePathSpecExampleResolution,
     TrailingSeparatorReachesEveryFileTheDirectoryHolds) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib1/lib.map", "./rtl/");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib1/rtl/a.v lib1/rtl/b.v");
}

TEST(FilePathSpecExampleResolution,
     TrailingSeparatorDoesNotReachBelowTheDirectory) {
  ScratchDir tmp;
  WriteTree(tmp);
  auto deeper = tmp.Write("lib1/rtl/sub/c.v", "module c;\nendmodule\n");
  ExampleMap m(tmp, "lib1/lib.map", "./rtl/");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.map.LibraryForFile(deeper.string()), "work");
}

TEST(FilePathSpecExampleMapping,
     TrailingSeparatorWritesTheDirectorysFilesIntoTheLibrary) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib1/lib.map", "./rtl/");
  ASSERT_TRUE(m.loaded);

  TaggedFile rtl_a(m.map, tmp.dir / "lib1/rtl/a.v");
  TaggedFile rtl_b(m.map, tmp.dir / "lib1/rtl/b.v");
  TaggedFile gate_a(m.map, tmp.dir / "lib2/gates/a.v");
  ASSERT_FALSE(rtl_a.diag.HasErrors());
  ASSERT_FALSE(rtl_b.diag.HasErrors());
  ASSERT_FALSE(gate_a.diag.HasErrors());

  EXPECT_EQ(rtl_a.Library(), "exLib");
  EXPECT_EQ(rtl_b.Library(), "exLib");
  EXPECT_EQ(gate_a.Library(), "work");
}

TEST(FilePathSpecExampleMapping,
     SharedFileGoesToTheSpecWhoseEndingIsMoreSpecific) {
  ScratchDir tmp;
  WriteTree(tmp);
  SharedFileMap m(tmp, "lib.map", Rooted(tmp, "lib*/*/a.v"), ".../rtl/*.v");
  ASSERT_TRUE(m.loaded);

  TaggedFile rtl_a(m.map, tmp.dir / "lib1/rtl/a.v");
  TaggedFile gate_a(m.map, tmp.dir / "lib2/gates/a.v");
  TaggedFile rtl_b(m.map, tmp.dir / "lib1/rtl/b.v");
  TaggedFile gate_b(m.map, tmp.dir / "lib2/gates/b.v");
  ASSERT_FALSE(rtl_a.diag.HasErrors());
  ASSERT_FALSE(gate_a.diag.HasErrors());
  ASSERT_FALSE(rtl_b.diag.HasErrors());
  ASSERT_FALSE(gate_b.diag.HasErrors());

  EXPECT_EQ(rtl_a.Library(), "firstLib");
  EXPECT_EQ(gate_a.Library(), "firstLib");
  EXPECT_EQ(rtl_b.Library(), "secondLib");
  EXPECT_EQ(gate_b.Library(), "work");
}

TEST(FilePathSpecExampleMapping,
     DirectoryEndingKeepsOnlyWhatTheWildcardedNameDoesNotReach) {
  ScratchDir tmp;
  WriteTree(tmp);
  auto longer = tmp.Write("lib1/rtl/ab.v", "module ab;\nendmodule\n");
  SharedFileMap m(tmp, "lib1/lib.map", "./rtl/?.v", "./rtl/");
  ASSERT_TRUE(m.loaded);

  TaggedFile rtl_a(m.map, tmp.dir / "lib1/rtl/a.v");
  TaggedFile rtl_ab(m.map, longer);
  TaggedFile gate_a(m.map, tmp.dir / "lib2/gates/a.v");
  ASSERT_FALSE(rtl_a.diag.HasErrors());
  ASSERT_FALSE(rtl_ab.diag.HasErrors());
  ASSERT_FALSE(gate_a.diag.HasErrors());

  EXPECT_EQ(rtl_a.Library(), "firstLib");
  EXPECT_EQ(rtl_ab.Library(), "secondLib");
  EXPECT_EQ(gate_a.Library(), "work");
}

}  // namespace
