// Tests for IEEE 1800-2023 §33.8.3 "Resolving multiple path specifications".
//
// The subclause fixes one library map -- four libraries, each declared with a
// single file path specification -- and then states, for six source file
// names, which library each maps into when the map is evaluated from a
// directory beside the one the specifications reach. Every one of those six
// lines is a declarative requirement of its own, so they are enumerated here
// as claims 1 through 6, with the shape of the map as claim 0:
//
//   0. Each of the four specifications is written between double quotes. A
//      path so written is the path the quotes surround, so the map declares
//      the same four libraries the bare spelling would, and none of the six
//      lines below holds otherwise.
//   1. A name reached by a wildcarded file name and by a directory maps into
//      the library the wildcarded name was declared for.
//   2. A name reached by a file name written out, by a wildcarded file name
//      and by a directory maps into the library the written-out name was
//      declared for.
//   3. A name no file name reaches, wildcarded or not, maps into the library
//      the directory was declared for.
//   4. The wildcard in a wildcarded file name opens it as readily as it closes
//      it: a name reached by a specification whose wildcard leads still
//      outranks the directory that also reaches it.
//   5. A name two libraries reach through wildcarded file names is an error,
//      neither library claiming it.
//   6. A name no specification of the map reaches at all is compiled into the
//      default library.
//
// All six are applied at the parser stage, by LibraryMap::LibraryForFile
// (src/parser/library_map.cpp), which ranks the specifications matching a name
// and reports the library the winner was declared for -- or no library where
// the winners disagree, or the default library where nothing matched. Claim 0
// is applied one layer down, by the file path resolution
// LibraryMap::ResolveSpec and LibraryMap::PathMatches carry out for it, since
// what a quoted specification reaches is decided when the path it names is
// read out of it.
//
// The inputs the claims consume come from this pass's dependencies. §33.3.1 is
// where a library declaration and its file path specification come from, and
// where a name matching nothing is said to be compiled into work; §33.3.1.1 is
// the ranking claims 1 through 5 turn on -- a file name written out first, a
// wildcarded file name next, a directory last, and two libraries left level
// an error. Every test therefore writes the subclause's four declarations into
// a real library map on disk and loads it through LibraryMap::LoadMapFile, so
// the specifications under test are lexed and parsed out of library_text
// rather than handed to the resolver directly.
//
// The subclause's map mixes the ways a specification can be anchored: three of
// the four are written from the root of the filesystem and the fourth is
// written relative, opening with a parent step. What a relative one is
// resolved from is the directory holding the map file it was declared in, so
// the map file goes into the directory the subclause evaluates from, one step
// away from the directory the other three name. A scratch directory stands in
// for the root, so the rooted specifications are written from it.
//
// The rejecting side of each claim is another of the claims: claim 3 is a name
// the wildcarded specifications of claims 1 and 4 do not reach, claim 5 is the
// tie claims 1, 2 and 4 avoid, and claim 6 is a name outside the map
// altogether. Claim 0 is rejected by its own closest input, a specification
// opened with a quote and closed without one, which is a path beginning with a
// quote and reaches nothing.
//
// The tests then carry the six lines the whole way a compiler carries a source
// file, in two layers. The first reads each file, lexes it, parses it and tags
// it through the map, which writes the cells the file describes into whichever
// library the file name resolved to. The second hands the same map and the
// same files to SinglePassCompiler, the driver that reads a description off
// disk, maps it and writes its cells into a library, and reads the answers
// back out of the libraries themselves -- which is where §33.3.1 and §33.3.1.1
// each supply an input in their own syntax and every layer between the
// declaration and the written cell is production code. Each of the six files
// describes one cell and nothing distinguishes the files but their names, so a
// library on any of those cells is that resolution's doing.
//
// The driver is also the layer at which claim 5 is an error rather than an
// absence. The resolver reports a name two libraries are level on by naming no
// library for it, and it is the driver that turns that into a rejected
// description, so the claim is read at both.

#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_scratch_dir.h"
#include "fixture_tagged_file.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/library_map.h"
#include "parser/parser.h"
#include "parser/single_pass_compile.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

// The six source files of the subclause's list, as paths relative to the
// directory standing in for the root of the filesystem. Five sit in the
// directory the map's specifications reach and one sits outside it entirely.
// The subclause writes the first of them relative to the directory it
// evaluates from; written out from the root it is this same file.
constexpr std::string_view kFooBar = "proj/lib/foobar.v";
constexpr std::string_view kFoo = "proj/lib/foo.v";
constexpr std::string_view kBar = "proj/lib/bar.v";
constexpr std::string_view kBarVer = "proj/lib/barver.v";
constexpr std::string_view kFooVer = "proj/lib/foover.v";
constexpr std::string_view kTb = "test/tb/tb.v";

// Where the map file goes: the directory the subclause evaluates from, which
// is a sibling of the one its specifications reach rather than an ancestor of
// it, so a relative specification declared there has to step out before it
// steps back in.
constexpr std::string_view kMapPath = "proj/tb/lib.map";

// Writes the six source files under `tmp`. Each describes one cell named for
// the file holding it, so the library a cell ends up in reports which library
// its file name resolved to.
void WriteSources(ScratchDir& tmp) {
  for (auto rel : {kFooBar, kFoo, kBar, kBarVer, kFooVer, kTb}) {
    std::string name(fs::path(std::string(rel)).stem().string());
    tmp.Write(std::string(rel), "module " + name + ";\nendmodule\n");
  }
}

// Writes the subclause's four library declarations into a map file in the
// directory it evaluates from and answers where the file went. `quote` decides
// whether each specification is written between double quotes, as the
// subclause writes them, or bare; both spellings name the same four paths,
// which is claim 0.
//
// Three of the specifications are written from the root of the filesystem, so
// they are built from the scratch directory standing in for it; the fourth is
// written relative and stands as the subclause writes it.
fs::path WriteSubclauseMap(ScratchDir& tmp, bool quote) {
  std::string q = quote ? "\"" : "";
  std::string lib = tmp.dir.string() + "/proj/lib/";
  std::string text;
  text += "library lib1 " + q + lib + "foo*.v" + q + ";\n";
  text += "library lib2 " + q + lib + "foo.v" + q + ";\n";
  text += "library lib3 " + q + "../lib/" + q + ";\n";
  text += "library lib4 " + q + lib + "*ver.v" + q + ";\n";
  return tmp.Write(std::string(kMapPath), text);
}

// That map loaded, which is the four declarations lexed and parsed out of
// library_text rather than handed to the resolver as strings.
struct SubclauseMap {
  LibraryMap map;
  bool loaded = false;

  SubclauseMap(ScratchDir& tmp, bool quote) {
    loaded = map.LoadMapFile(WriteSubclauseMap(tmp, quote));
  }

  // The library one of the six source file names maps into, or an empty view
  // where the specifications reaching it were declared for libraries the
  // ranking leaves level.
  std::string_view LibraryOf(const ScratchDir& tmp,
                             std::string_view rel) const {
    return map.LibraryForFile((tmp.dir / std::string(rel)).string());
  }
};

// The full path of one of the six source files.
fs::path SourcePath(const ScratchDir& tmp, std::string_view rel) {
  return tmp.dir / std::string(rel);
}

// Everything a compile writes into, and the compiler that writes into it. The
// driver reads a named description off disk, asks the library map which
// library its name resolves to, and writes the cells it declares there, so a
// cell read back out of a library has been through every layer between a
// library declaration and a written cell.
struct CompileHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap libs;
  CompilationUnit unit;
  SinglePassCompiler compiler{libs, mgr, arena, diag};
};

// Claim 0: each of the subclause's four specifications is written between
// double quotes, and every line it goes on to state is a line about the paths
// those quotes surround, so the same four declarations with the quotes dropped
// declare the same four libraries.
//
// Which library each of the quoted specifications reaches is what claims 1
// through 6 read below, every one of them off the quoted map the subclause
// writes; what is left for this test is the other spelling, so the two maps
// are read against each other rather than against literals. Both ways a
// specification can be anchored are covered -- a name reached by a rooted
// specification and a name reached by the relative one that opens with a
// parent step -- since the quotes come off before the anchoring is looked at.
TEST(ResolveMultiplePathSpecs, BareSpecNamesWhatTheQuotedSpellingNames) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap quoted(tmp, /*quote=*/true);
  SubclauseMap bare(tmp, /*quote=*/false);
  ASSERT_TRUE(quoted.loaded);
  ASSERT_TRUE(bare.loaded);
  EXPECT_EQ(bare.LibraryOf(tmp, kFoo), quoted.LibraryOf(tmp, kFoo));
  EXPECT_EQ(bare.LibraryOf(tmp, kBar), quoted.LibraryOf(tmp, kBar));
}

// Claim 0, negative: what makes a specification quoted is the pair. Opened
// with a quote and closed without one, the quote is a character of the path
// instead, and no path under the tree begins with one -- so the specification
// that would have reached the wildcarded names reaches nothing, and the
// directory declared for lib3 is left holding them.
TEST(ResolveMultiplePathSpecs, UnclosedQuoteIsPartOfThePathRatherThanNotation) {
  ScratchDir tmp;
  WriteSources(tmp);
  std::string text = "library lib1 \"";
  text += tmp.dir.string() + "/proj/lib/foo*.v;\n";
  text += "library lib3 \"../lib/\";\n";
  LibraryMap map;
  ASSERT_TRUE(map.LoadMapFile(tmp.Write(std::string(kMapPath), text)));
  auto path = (tmp.dir / std::string(kFooBar)).string();
  EXPECT_EQ(map.LibraryForFile(path), "lib3");
}

// Claim 1: two libraries reach this name, one through a file name carrying a
// wildcard and one through a directory. A wildcarded file name is the more
// specific ending of the two, so the name maps into the library it was
// declared for.
TEST(ResolveMultiplePathSpecs, WildcardedFileNameOutranksADirectory) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap m(tmp, /*quote=*/true);
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.LibraryOf(tmp, kFooBar), "lib1");
}

// Claim 2: three libraries reach this name -- one through a file name written
// out, one through a wildcarded file name whose wildcard stands for nothing at
// all, one through a directory. The written-out name is the most specific
// ending there is, so the name maps into the library declared for it and
// neither of the other two.
TEST(ResolveMultiplePathSpecs, WrittenOutFileNameOutranksBothOtherEndings) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap m(tmp, /*quote=*/true);
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.LibraryOf(tmp, kFoo), "lib2");
}

// Claim 3: the one name of the five in that directory that no file name of the
// map reaches. The directory ending is the least specific of the three and is
// still what maps the name, so the lowest of the rankings resolves a name on
// its own rather than only losing to the others.
TEST(ResolveMultiplePathSpecs, DirectoryResolvesWhatNoFileNameReaches) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap m(tmp, /*quote=*/true);
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.LibraryOf(tmp, kBar), "lib3");
}

// Claim 4: this name is reached by a wildcarded file name whose wildcard opens
// it rather than closing it, and by the directory. Where the wildcard stands
// in the name does not enter into the ranking -- the ending is a wildcarded
// file name either way -- so the name maps into the library declared for it,
// as in claim 1.
TEST(ResolveMultiplePathSpecs, LeadingWildcardIsStillAWildcardedFileName) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap m(tmp, /*quote=*/true);
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.LibraryOf(tmp, kBarVer), "lib4");
}

// Claim 5: the name claims 1 and 4 each reach half of. Both specifications end
// in a wildcarded file name, so the ranking leaves the two libraries level and
// nothing chooses between them; the directory that also reaches the name does
// not rescue it, being the less specific ending. The name is an error, which
// is read back as neither library claiming it.
TEST(ResolveMultiplePathSpecs, TwoLibrariesLevelOnOneNameIsAnError) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap m(tmp, /*quote=*/true);
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.LibraryOf(tmp, kFooVer), "");
}

// Claim 6: the one name of the six outside the directory the map's
// specifications reach. Nothing in the map matches it, not even the directory
// ending that catches the other five, so it is compiled into the default
// library rather than being an error or belonging to whichever library was
// declared last.
TEST(ResolveMultiplePathSpecs, NameOutsideEverySpecGoesToTheDefaultLibrary) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap m(tmp, /*quote=*/true);
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.LibraryOf(tmp, kTb), "work");
}

// All six lines carried through to what a resolution is for. Each file is read
// off disk, lexed and parsed, and the cell it describes is written into the
// library its name resolved to, so every answer above is read back off a
// parsed description rather than off the resolver alone. The name two
// libraries are level on describes a cell that no library claims, and the name
// outside the map describes one in the default library.
TEST(ResolveMultiplePathSpecsMapping, EveryNameIsWrittenIntoTheLibraryItMaps) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap m(tmp, /*quote=*/true);
  ASSERT_TRUE(m.loaded);

  TaggedFile foobar(m.map, tmp.dir / std::string(kFooBar));
  TaggedFile foo(m.map, tmp.dir / std::string(kFoo));
  TaggedFile bar(m.map, tmp.dir / std::string(kBar));
  TaggedFile barver(m.map, tmp.dir / std::string(kBarVer));
  TaggedFile foover(m.map, tmp.dir / std::string(kFooVer));
  TaggedFile tb(m.map, tmp.dir / std::string(kTb));
  ASSERT_FALSE(foobar.diag.HasErrors());
  ASSERT_FALSE(foo.diag.HasErrors());
  ASSERT_FALSE(bar.diag.HasErrors());
  ASSERT_FALSE(barver.diag.HasErrors());
  ASSERT_FALSE(foover.diag.HasErrors());
  ASSERT_FALSE(tb.diag.HasErrors());

  EXPECT_EQ(foobar.Library(), "lib1");
  EXPECT_EQ(foo.Library(), "lib2");
  EXPECT_EQ(bar.Library(), "lib3");
  EXPECT_EQ(barver.Library(), "lib4");
  EXPECT_EQ(foover.Library(), "");
  EXPECT_EQ(tb.Library(), "work");
}

// End to end over what §33.3.1.1 supplies, which is the ranking claims 1
// through 4 turn on. The four names it resolves are handed to the compile
// driver as a command line, and each is read off disk, mapped and written into
// a library by production code; the answers are then read back out of the
// libraries rather than off the resolver. Every one of the ranking's endings
// decides one of the four, and each of the lower-ranked libraries whose
// specification also reached a name is read back holding nothing of it.
TEST(ResolveMultiplePathSpecsCompile, EachNameIsWrittenIntoItsRankedLibrary) {
  ScratchDir tmp;
  WriteSources(tmp);
  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(WriteSubclauseMap(tmp, /*quote=*/true)));
  ASSERT_TRUE(h.compiler.CompileCommandLine(
      {SourcePath(tmp, kFooBar), SourcePath(tmp, kFoo), SourcePath(tmp, kBar),
       SourcePath(tmp, kBarVer)},
      h.unit));

  EXPECT_NE(h.libs.CellInLibrary("lib1", "foobar"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("lib2", "foo"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("lib3", "bar"), nullptr);
  EXPECT_NE(h.libs.CellInLibrary("lib4", "barver"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("lib3", "foobar"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("lib1", "foo"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("lib3", "foo"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("lib3", "barver"), nullptr);
}

// Claim 5 read where it is an error rather than an absence. The resolver
// answers a name two libraries are level on by naming no library for it, and
// the driver is what turns that into a rejected description: the compile
// fails, an error is raised, nothing of the description reaches either of the
// two libraries, and no cell of it joins the unit a design would bind in.
TEST(ResolveMultiplePathSpecsCompile, ANameTwoLibrariesAreLevelOnIsRejected) {
  ScratchDir tmp;
  WriteSources(tmp);
  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(WriteSubclauseMap(tmp, /*quote=*/true)));

  EXPECT_EQ(h.compiler.CompileSource(SourcePath(tmp, kFooVer), h.unit),
            CompileOutcome::kFailed);
  // §33.3.1.1 is what makes the level claim an error, so that is the subclause
  // the report names; it stands at the first of the two declarations making
  // the claim, which is lib1's on line 1 of the map file.
  EXPECT_TRUE(ReportedError(
      h.diag.Diagnostics(),
      "source description claimed by more than one library (lib1, lib4): ", 1,
      "33.3.1.1"));
  EXPECT_EQ(h.libs.CellInLibrary("lib1", "foover"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("lib4", "foover"), nullptr);
  EXPECT_TRUE(h.unit.modules.empty());
}

// End to end over what §33.3.1 supplies, which is a library declaration and
// the library a name no declaration reaches belongs to. The name outside the
// map compiles rather than failing -- it is not an ambiguity -- and its cell
// is written into the default library, not into the one whose directory
// specification catches the five names beside it.
TEST(ResolveMultiplePathSpecsCompile, UnmatchedNameIsWrittenIntoTheDefault) {
  ScratchDir tmp;
  WriteSources(tmp);
  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(WriteSubclauseMap(tmp, /*quote=*/true)));

  EXPECT_EQ(h.compiler.CompileSource(SourcePath(tmp, kTb), h.unit),
            CompileOutcome::kCompiled);
  EXPECT_FALSE(h.diag.HasErrors());
  EXPECT_NE(h.libs.CellInLibrary("work", "tb"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("lib3", "tb"), nullptr);
}

}  // namespace
