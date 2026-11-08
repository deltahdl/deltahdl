#include <gtest/gtest.h>
#include <unistd.h>

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <initializer_list>
#include <string>
#include <string_view>
#include <system_error>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/library_map.h"
#include "parser/parser.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

struct ParsedMap {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Arena arena;
  CompilationUnit* cu = nullptr;

  explicit ParsedMap(const std::string& text) {
    uint32_t fid = mgr.AddFile("lib.map", text);
    Lexer lexer(mgr.FileContent(fid), fid, diag);
    Parser parser(lexer, arena, diag);
    cu = parser.ParseLibraryText();
  }
};

LibraryDecl MakeDecl(std::string_view name,
                     std::initializer_list<std::string_view> paths) {
  LibraryDecl d;
  d.name = name;
  for (auto p : paths) d.file_paths.push_back(p);
  return d;
}

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

TEST(LibraryMapWildcards, QuestionDoesNotMatchMissingCharacter) {
  LibraryMap m;
  auto rtl = MakeDecl("rtlLib", {"a?.v"});
  m.AddDeclaration(rtl, "/proj/rtl");
  EXPECT_EQ(m.LibraryForFile("/proj/rtl/a.v"), "work");
}

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

TEST(LibraryMapPathMatches, SpecWildcardedFromTheRootMatches) {
  EXPECT_TRUE(LibraryMap::PathMatches("/*.v", "/proj", "/a.v"));
  EXPECT_FALSE(LibraryMap::PathMatches("/*.v", "/proj", "/a.sv"));
}

TEST(LibraryMapPathMatches, RelativeSpecWithNoBaseMatchesARelativePath) {
  EXPECT_TRUE(LibraryMap::PathMatches("rtl/*.v", "", "rtl/a.v"));
  EXPECT_FALSE(LibraryMap::PathMatches("rtl/*.v", "", "gates/a.v"));
}

TEST(LibraryMapFileReading, ReadsMappingFromPredefinedFile) {
  ScratchMapDir tmp;
  auto map_file = tmp.Write("lib.map", "library rtlLib *.v;\n");

  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(map_file));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "rtlLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.sv").string()), "work");
}

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

TEST(LibraryMapFileReading, NonexistentMapFileReportsFailure) {
  ScratchMapDir tmp;
  LibraryMap m;
  std::vector<std::string> errors;
  EXPECT_FALSE(m.LoadMapFile(tmp.dir / "absent.map", &errors));
  EXPECT_FALSE(errors.empty());
}

TEST(LibraryMapFileReading, MalformedMapFileReportsFailure) {
  ScratchMapDir tmp;
  auto bad = tmp.Write("lib.map", "library;\n");
  LibraryMap m;
  std::vector<std::string> errors;
  EXPECT_FALSE(m.LoadMapFile(bad, &errors));
  EXPECT_FALSE(errors.empty());
}

TEST(LibraryMapDeclSyntax, CommaSeparatedPathsAllMapToLibrary) {
  ScratchMapDir tmp;
  auto map_file = tmp.Write("lib.map", "library multiLib a.v, b.v, c.v;\n");

  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(map_file));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "a.v").string()), "multiLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "b.v").string()), "multiLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "c.v").string()), "multiLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "d.v").string()), "work");
}

TEST(LibraryMapIncludeStatement, IncludePullsInAnotherMapFile) {
  ScratchMapDir tmp;
  tmp.Write("sub.map", "library incLib *.v;\n");
  auto top = tmp.Write("lib.map", "include sub.map;\n");

  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "incLib");
}

TEST(LibraryMapEmptyDescription, StraySemicolonsAreSkipped) {
  ScratchMapDir tmp;
  auto map_file = tmp.Write("lib.map", ";\nlibrary rtlLib *.v;\n;\n");

  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(map_file));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "rtlLib");
}

TEST(LibraryMapDeclSyntax, IncdirClauseCapturesIncludeDirs) {
  ParsedMap p("library rtlLib *.v -incdir ./inc, ../shared;\n");
  ASSERT_FALSE(p.diag.HasErrors());
  ASSERT_EQ(p.cu->libraries.size(), 1u);
  const LibraryDecl* d = p.cu->libraries[0];
  EXPECT_EQ(d->name, "rtlLib");
  ASSERT_EQ(d->file_paths.size(), 1u);
  EXPECT_EQ(d->file_paths[0], "*.v");
  ASSERT_EQ(d->incdir_paths.size(), 2u);
  EXPECT_EQ(d->incdir_paths[0], "./inc");
  EXPECT_EQ(d->incdir_paths[1], "../shared");
}

TEST(LibraryMapConfigDescription, ConfigDeclarationParsedInLibraryText) {
  ParsedMap p(
      "config cfg1;\n"
      "  design rtlLib.top;\n"
      "endconfig\n");
  ASSERT_FALSE(p.diag.HasErrors());
  ASSERT_EQ(p.cu->configs.size(), 1u);
  EXPECT_EQ(p.cu->configs[0]->name, "cfg1");
  EXPECT_TRUE(p.cu->libraries.empty());
}

TEST(LibraryMapDeclSyntax, LibraryDeclWithoutPathIsRejected) {
  ScratchMapDir tmp;
  auto map_file = tmp.Write("lib.map", "library rtlLib;\n");

  LibraryMap m;
  std::vector<std::string> errors;
  EXPECT_FALSE(m.LoadMapFile(map_file, &errors));
  EXPECT_FALSE(errors.empty());
}

TEST(LibraryMapIncludeStatement, IncludeWithoutPathIsRejected) {
  ScratchMapDir tmp;
  auto map_file = tmp.Write("lib.map", "include ;\n");

  LibraryMap m;
  std::vector<std::string> errors;
  EXPECT_FALSE(m.LoadMapFile(map_file, &errors));
  EXPECT_FALSE(errors.empty());
}

TEST(LibraryMapFileReading, SourceNamedThroughASymbolicLinkMatches) {
  ScratchMapDir tmp;
  tmp.Write("real/lib.map", "library rtlLib *.v;\n");
  fs::path real = tmp.dir / "real";
  fs::path link = tmp.dir / "link";
  std::error_code ec;
  fs::create_directory_symlink(real, link, ec);
  ASSERT_FALSE(ec) << ec.message();

  LibraryMap through_link;
  ASSERT_TRUE(through_link.LoadMapFile(link / "lib.map"));
  EXPECT_EQ(through_link.LibraryForFile((real / "top.v").string()), "rtlLib");

  LibraryMap direct;
  ASSERT_TRUE(direct.LoadMapFile(real / "lib.map"));
  EXPECT_EQ(direct.LibraryForFile((link / "top.v").string()), "rtlLib");
}

TEST(LibraryMapFileReading, SpecNamingItsDirectoryThroughASymbolicLinkMatches) {
  ScratchMapDir tmp;
  fs::create_directories(tmp.dir / "real");
  fs::path link = tmp.dir / "link";
  std::error_code ec;
  fs::create_directory_symlink(tmp.dir / "real", link, ec);
  ASSERT_FALSE(ec) << ec.message();
  tmp.Write("lib.map", "library L " + (link / "*.v").string() + ";\n");

  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(tmp.dir / "lib.map"));
  EXPECT_EQ(m.LibraryForFile((link / "a.v").string()), "L");
}

}  // namespace
