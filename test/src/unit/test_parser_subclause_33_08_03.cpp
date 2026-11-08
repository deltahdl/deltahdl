#include <gtest/gtest.h>

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
#include "parser/library_map.h"
#include "parser/single_pass_compile.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

constexpr std::string_view kFooBar = "proj/lib/foobar.v";
constexpr std::string_view kFoo = "proj/lib/foo.v";
constexpr std::string_view kBar = "proj/lib/bar.v";
constexpr std::string_view kBarVer = "proj/lib/barver.v";
constexpr std::string_view kFooVer = "proj/lib/foover.v";
constexpr std::string_view kTb = "test/tb/tb.v";

constexpr std::string_view kMapPath = "proj/tb/lib.map";

void WriteSources(ScratchDir& tmp) {
  for (auto rel : {kFooBar, kFoo, kBar, kBarVer, kFooVer, kTb}) {
    std::string name(fs::path(std::string(rel)).stem().string());
    tmp.Write(std::string(rel), "module " + name + ";\nendmodule\n");
  }
}

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

struct SubclauseMap {
  LibraryMap map;
  bool loaded = false;

  SubclauseMap(ScratchDir& tmp, bool quote) {
    loaded = map.LoadMapFile(WriteSubclauseMap(tmp, quote));
  }

  std::string_view LibraryOf(const ScratchDir& tmp,
                             std::string_view rel) const {
    return map.LibraryForFile((tmp.dir / std::string(rel)).string());
  }
};

fs::path SourcePath(const ScratchDir& tmp, std::string_view rel) {
  return tmp.dir / std::string(rel);
}

struct CompileHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap libs;
  CompilationUnit unit;
  SinglePassCompiler compiler{libs, mgr, arena, diag};
};

TEST(ResolveMultiplePathSpecs, BareSpecNamesWhatTheQuotedSpellingNames) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap quoted(tmp, true);
  SubclauseMap bare(tmp, false);
  ASSERT_TRUE(quoted.loaded);
  ASSERT_TRUE(bare.loaded);
  EXPECT_EQ(bare.LibraryOf(tmp, kFoo), quoted.LibraryOf(tmp, kFoo));
  EXPECT_EQ(bare.LibraryOf(tmp, kBar), quoted.LibraryOf(tmp, kBar));
}

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

TEST(ResolveMultiplePathSpecs, WildcardedFileNameOutranksADirectory) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap m(tmp, true);
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.LibraryOf(tmp, kFooBar), "lib1");
}

TEST(ResolveMultiplePathSpecs, WrittenOutFileNameOutranksBothOtherEndings) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap m(tmp, true);
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.LibraryOf(tmp, kFoo), "lib2");
}

TEST(ResolveMultiplePathSpecs, DirectoryResolvesWhatNoFileNameReaches) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap m(tmp, true);
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.LibraryOf(tmp, kBar), "lib3");
}

TEST(ResolveMultiplePathSpecs, LeadingWildcardIsStillAWildcardedFileName) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap m(tmp, true);
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.LibraryOf(tmp, kBarVer), "lib4");
}

TEST(ResolveMultiplePathSpecs, TwoLibrariesLevelOnOneNameIsAnError) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap m(tmp, true);
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.LibraryOf(tmp, kFooVer), "");
}

TEST(ResolveMultiplePathSpecs, NameOutsideEverySpecGoesToTheDefaultLibrary) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap m(tmp, true);
  ASSERT_TRUE(m.loaded);
  EXPECT_EQ(m.LibraryOf(tmp, kTb), "work");
}

TEST(ResolveMultiplePathSpecsMapping, EveryNameIsWrittenIntoTheLibraryItMaps) {
  ScratchDir tmp;
  WriteSources(tmp);
  SubclauseMap m(tmp, true);
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

TEST(ResolveMultiplePathSpecsCompile, EachNameIsWrittenIntoItsRankedLibrary) {
  ScratchDir tmp;
  WriteSources(tmp);
  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(WriteSubclauseMap(tmp, true)));
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

TEST(ResolveMultiplePathSpecsCompile, ANameTwoLibrariesAreLevelOnIsRejected) {
  ScratchDir tmp;
  WriteSources(tmp);
  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(WriteSubclauseMap(tmp, true)));

  EXPECT_EQ(h.compiler.CompileSource(SourcePath(tmp, kFooVer), h.unit),
            CompileOutcome::kFailed);
  EXPECT_TRUE(ReportedError(
      h.diag.Diagnostics(),
      "source description claimed by more than one library (lib1, lib4): ", 1,
      "33.3.1.1"));
  EXPECT_EQ(h.libs.CellInLibrary("lib1", "foover"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("lib4", "foover"), nullptr);
  EXPECT_TRUE(h.unit.modules.empty());
}

TEST(ResolveMultiplePathSpecsCompile, UnmatchedNameIsWrittenIntoTheDefault) {
  ScratchDir tmp;
  WriteSources(tmp);
  CompileHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(WriteSubclauseMap(tmp, true)));

  EXPECT_EQ(h.compiler.CompileSource(SourcePath(tmp, kTb), h.unit),
            CompileOutcome::kCompiled);
  EXPECT_FALSE(h.diag.HasErrors());
  EXPECT_NE(h.libs.CellInLibrary("work", "tb"), nullptr);
  EXPECT_EQ(h.libs.CellInLibrary("lib3", "tb"), nullptr);
}

}  // namespace
