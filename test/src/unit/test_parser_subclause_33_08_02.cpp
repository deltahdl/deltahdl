// Tests for IEEE 1800-2023 §33.8.2 "File path specification examples".
//
// The subclause fixes a set of four source files -- two descriptions of a cell
// a and two of a cell b, one of each under lib1/rtl and one of each under
// lib2/gates -- and then states, for seven file path specifications, exactly
// which of those files each specification resolves to. Every one of those
// seven lines is a declarative requirement of its own, so they are enumerated
// here as claims 1 through 7:
//
//   From the directory holding the project (the subclause writes it /proj):
//     1. lib*/*/a.v rooted at that directory reaches both descriptions of a.
//        A multiple-character wildcard stands in a directory-name position
//        here, twice over, and each occurrence covers one name.
//     2. .../a.v reaches both descriptions of a. The hierarchical wildcard
//        opens a specification that names no directory at all.
//     3. An absolute .../b.v under that directory reaches both descriptions of
//        b, with the hierarchical wildcard between a rooted prefix and a file
//        name.
//     4. .../rtl/*.v reaches the two files under rtl and neither file under
//        gates: a hierarchical wildcard followed by a named directory covers
//        only the descents that arrive at that name.
//   From the lib1 directory:
//     5. ../lib2/gates/*.v reaches the two files under gates, so a parent step
//        opens a specification reaching into a sibling directory.
//     6. ./rtl/?.v reaches the two files under rtl, each of whose names carries
//        exactly one character where the single-character wildcard stands.
//     7. ./rtl/ reaches those same two files, a trailing separator covering
//        what the directory holds.
//
// All seven are applied at the parser stage, by the file path resolution
// LibraryMap::ResolveSpec and LibraryMap::PathMatches carry out for
// LibraryMap::LibraryForFile (src/parser/library_map.cpp). What a
// specification is resolved from is the directory holding the library map file
// it was declared in, which is how the tests below say which of the
// subclause's two vantage points a claim is being read from: the map file goes
// to the root of the tree for claims 1 through 4 and into lib1 for claims 5
// through 7.
//
// The input each claim consumes is a file_path_spec, and §33.3.1.1 -- this
// pass's dependency -- is where one comes from and how one that reaches a file
// several ways is settled. Every test therefore writes a real library map on
// disk and loads it through LibraryMap::LoadMapFile, so the specification under
// test is lexed and parsed out of library_text rather than handed to the
// resolver directly. One library is declared per map, so nothing a test reads
// back was decided by the precedence between specifications; what a claim
// reports is the resolution alone.
//
// A claim of the form "this specification resolves to these files" is a claim
// about a set, so the accepting and the rejecting side are read back together:
// Reached() answers which of the four files the declared library holds, and a
// file the specification does not reach is absent from that answer. Where the
// closest rejected input is a file the subclause's own tree does not hold --
// a longer file name for claim 6, a directory below rtl for claims 4 and 7 --
// a test writes that file beside the tree and reads back that no library
// claimed it.
//
// The subclause sorts its seven lines into a rooted group and a relative one,
// and what makes the first group rooted is that the directory a specification
// was declared in does not enter into it. A map file at the top of the tree
// cannot report that, since there a rooted specification and one resolved
// against the top reach the same files either way, so claims 1 and 3 are read
// from a map declared further down instead -- the answer the subclause states
// for each, arrived at from a vantage point that could not have produced it by
// accident.
//
// §33.3.1.1 is also what settles a file that more than one specification
// reaches, ranking the specifications by how their endings finish -- a file
// name written out, a wildcarded one, a directory. Two of the subclause's own
// lines share a file with two others, so the last two tests declare such a
// pair together and carry every description the whole way, from the file on
// disk to the library its cell was written into. That is this pass's
// dependency supplying the input in its own syntax rather than a resolution
// read back on its own.

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <filesystem>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_scratch_dir.h"
#include "fixture_tagged_file.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/library_map.h"
#include "parser/parser.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

// The four files of the subclause's tree, in the order it lists them, as paths
// relative to the directory standing in for its /proj. Reading a resolution
// back in this order lets an expectation be written as the subclause writes
// its right-hand sides.
constexpr std::array<std::string_view, 4> kTreePaths = {
    "lib1/rtl/a.v", "lib2/gates/a.v", "lib1/rtl/b.v", "lib2/gates/b.v"};

// The descriptions those files hold. Each file describes the cell its name
// carries, so a compiler that reaches one has a cell to write into whichever
// library the specification resolved to.
constexpr const char* kCellA = "module a;\nendmodule\n";
constexpr const char* kCellB = "module b;\nendmodule\n";

// Writes the subclause's tree under `tmp`, the directory standing in for the
// project root.
void WriteTree(ScratchDir& tmp) {
  tmp.Write("lib1/rtl/a.v", kCellA);
  tmp.Write("lib2/gates/a.v", kCellA);
  tmp.Write("lib1/rtl/b.v", kCellB);
  tmp.Write("lib2/gates/b.v", kCellB);
}

// A library map declaring `spec` as the sole file path specification of a
// library exLib, written at `map_rel` under the tree and loaded from there.
// The directory a relative specification is resolved from is the one holding
// the map file, so `map_rel` is how a test names the vantage point the
// subclause is reading from: "lib.map" for the project root, "lib1/lib.map"
// for the lib1 directory.
struct ExampleMap {
  LibraryMap map;
  bool loaded = false;

  ExampleMap(ScratchDir& tmp, const std::string& map_rel,
             const std::string& spec) {
    auto map_file = tmp.Write(map_rel, "library exLib " + spec + ";\n");
    loaded = map.LoadMapFile(map_file);
  }
};

// A library map declaring two of the subclause's specifications side by side,
// one as firstLib and one as secondLib. Where both reach one file, which
// library ends up holding it is settled by the precedence §33.3.1.1 gives
// their endings, so this is the shape a test takes when it builds its input
// out of what this pass's dependency supplies.
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

// Which of the tree's four files the declared library holds, as one
// space-separated list in the order the subclause lists the tree. A file the
// specification did not reach falls to the default library instead and so is
// absent from the answer.
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

// The absolute form of a path under the tree, for the specifications the
// subclause writes rooted rather than relative.
std::string Rooted(const ScratchDir& tmp, const std::string& tail) {
  return tmp.dir.string() + "/" + tail;
}

// Claim 1, negative: the wildcard covers a name, not a run of them. Dropping
// one of the two wildcarded positions leaves a specification naming a file
// directly below lib1 and lib2, and the tree holds none, so the specification
// reaches nothing at all rather than reaching down through rtl and gates.
TEST(FilePathSpecExampleResolution,
     WildcardedDirectoryNameDoesNotSpanTwoDirectories) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib.map", Rooted(tmp, "lib*/a.v"));
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "");
}

// Claim 1: a specification wildcarding two successive directory names reaches
// the file of that name under every pair of directories, which is both
// descriptions of cell a and neither of cell b. It is read from lib1 rather
// than from the top of the tree because a rooted specification says where it
// begins, so the directory holding the map file it was declared in does not
// enter into it -- and one of the two files it still reaches lies outside lib1
// altogether, where a relative specification declared there reaches only what
// lies below it, as the claim 5 negative reads back. Read from the top the
// answer would be the same for either reason, which is what makes this the
// vantage point that reports the line.
TEST(FilePathSpecExampleResolution,
     RootedSpecReachesBothDescriptionsWhereverItIsDeclared) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib1/lib.map", Rooted(tmp, "lib*/*/a.v"));
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib1/rtl/a.v lib2/gates/a.v");
}

// Claim 2: a specification opening with the hierarchical wildcard names no
// directory of the tree, and reaches the file of that name however deep it
// lies under the directory being resolved from -- both descriptions of a.
TEST(FilePathSpecExampleResolution,
     HierarchicalWildcardOpeningASpecReachesEveryDepth) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib.map", ".../a.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib1/rtl/a.v lib2/gates/a.v");
}

// Claim 2, negative: that specification is still anchored, and what anchors it
// is the directory it is resolved from. Declared in a map file sitting in
// lib2, the same text reaches only what lies under lib2, so the description
// under lib1 is left to the default library.
TEST(FilePathSpecExampleResolution,
     HierarchicalWildcardIsAnchoredAtTheDirectoryResolvedFrom) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib2/lib.map", ".../a.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib2/gates/a.v");
}

// Claim 3, negative: the rooted prefix ahead of the wildcard is matched
// literally, so naming lib1 there leaves the description of b under lib2
// unreached.
TEST(FilePathSpecExampleResolution,
     HierarchicalWildcardDoesNotReachOutsideItsRootedPrefix) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib.map", Rooted(tmp, "lib1/.../b.v"));
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib1/rtl/b.v");
}

// Claim 3: the hierarchical wildcard stands between a rooted prefix and a file
// name just as readily as it opens a specification, and reaches both
// descriptions of cell b. What it descends from is that rooted prefix and not
// the directory the map file sits in, so the line is read from a vantage point
// as deep as the tree goes -- a directory holding one of the two files and
// standing beneath neither the other nor their common parent.
TEST(FilePathSpecExampleResolution,
     RootedHierarchicalWildcardReachesEveryDepthWhereverDeclared) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib2/gates/lib.map", Rooted(tmp, ".../b.v"));
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib1/rtl/b.v lib2/gates/b.v");
}

// Claim 4: a named directory after the hierarchical wildcard keeps only the
// descents arriving at that name, so the specification reaches both files
// under rtl and neither of the two under gates -- the one line of the seven
// whose answer holds a file of each cell rather than two of one.
TEST(FilePathSpecExampleResolution,
     NamedDirectoryAfterHierarchicalWildcardSelectsThatDirectory) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib.map", ".../rtl/*.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib1/rtl/a.v lib1/rtl/b.v");
}

// Claim 4, negative: only the leading wildcard descends. The wildcarded file
// name at the end covers a name in the named directory itself, so a file one
// directory further down is left to the default library even though the
// specification opened with a hierarchical wildcard.
TEST(FilePathSpecExampleResolution,
     WildcardedFileNameAfterHierarchicalWildcardStaysInOneDirectory) {
  ScratchDir tmp;
  WriteTree(tmp);
  auto deeper = tmp.Write("lib1/rtl/sub/c.v", "module c;\nendmodule\n");
  ExampleMap m(tmp, "lib.map", ".../rtl/*.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.map.LibraryForFile(deeper.string()), "work");
}

// Claim 5: resolved from lib1, a specification opening with a parent step
// reaches into the sibling directory, and its wildcarded file name covers both
// descriptions held under gates.
TEST(FilePathSpecExampleResolution, ParentStepReachesIntoASiblingDirectory) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib1/lib.map", "../lib2/gates/*.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib2/gates/a.v lib2/gates/b.v");
}

// Claim 5, negative: the parent step is what carries the specification out of
// lib1. Without it the same tail names a directory below lib1, which the tree
// does not hold, so the specification reaches nothing.
TEST(FilePathSpecExampleResolution,
     SpecWithoutTheParentStepStaysBelowItsOwnDirectory) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib1/lib.map", "lib2/gates/*.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "");
}

// Claim 6: resolved from lib1, a specification opening with the current
// directory and ending in the single-character wildcard reaches both files
// under rtl, each of whose names carries one character where the wildcard
// stands.
TEST(FilePathSpecExampleResolution,
     SingleCharacterWildcardReachesEveryOneCharacterName) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib1/lib.map", "./rtl/?.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib1/rtl/a.v lib1/rtl/b.v");
}

// Claim 6, negative: the wildcard stands for one character rather than for a
// run of them, so a longer name in the very directory the specification names
// is left to the default library.
TEST(FilePathSpecExampleResolution,
     SingleCharacterWildcardDoesNotReachALongerName) {
  ScratchDir tmp;
  WriteTree(tmp);
  auto longer = tmp.Write("lib1/rtl/ab.v", "module ab;\nendmodule\n");
  ExampleMap m(tmp, "lib1/lib.map", "./rtl/?.v");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.map.LibraryForFile(longer.string()), "work");
}

// Claim 7: a specification ending at a directory reaches what that directory
// holds, whatever the names are -- the same two files claim 6 reaches through
// a wildcarded name.
TEST(FilePathSpecExampleResolution,
     TrailingSeparatorReachesEveryFileTheDirectoryHolds) {
  ScratchDir tmp;
  WriteTree(tmp);
  ExampleMap m(tmp, "lib1/lib.map", "./rtl/");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(Reached(m, tmp), "lib1/rtl/a.v lib1/rtl/b.v");
}

// Claim 7, negative: what the directory holds is not what lies below it. A
// file one directory further down is left to the default library, which is
// what separates this line from the hierarchical wildcard of claims 2 to 4.
TEST(FilePathSpecExampleResolution,
     TrailingSeparatorDoesNotReachBelowTheDirectory) {
  ScratchDir tmp;
  WriteTree(tmp);
  auto deeper = tmp.Write("lib1/rtl/sub/c.v", "module c;\nendmodule\n");
  ExampleMap m(tmp, "lib1/lib.map", "./rtl/");
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.map.LibraryForFile(deeper.string()), "work");
}

// Claim 7 carried through to what a resolution is for. The directory the
// specification ends at holds one description of each cell, so once each file
// is read, lexed and parsed, both descriptions are written into the library
// the specification resolved to while the descriptions under gates are not.
// Nothing distinguishes the files but the directories they sit in, so a
// library on any of these cells is that resolution's doing.
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

// End to end over what §33.3.1.1 supplies, which is the ranking that settles a
// file more than one specification reaches. Claims 1 and 4 both reach the RTL
// description of a, and claim 1 finishes with a file name written out where
// claim 4 finishes with a wildcarded one, so that description goes to the
// library claim 1 declared. Everywhere the two lines do not overlap they
// resolve as the subclause states them: the gate-level a is claim 1's alone,
// the RTL b is claim 4's alone, and the gate-level b is outside both. Every
// answer is read off a cell parsed from the file it was resolved to, so this
// is also where claims 1 and 4 are carried through to a written library, as
// claim 7 is above.
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

// The same dependency across the other pair of endings, and from the other
// vantage point the subclause reads from. Claims 6 and 7 both reach the two
// one-character names under rtl; a wildcarded file name is the more specific
// of the two endings, so those descriptions go to the library claim 6
// declared. What claim 7 holds on its own is a longer name in that very
// directory, which is how the library that lost the shared files is read back
// still holding what the ranking left it rather than nothing at all.
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
