#include <gtest/gtest.h>
#include <unistd.h>

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>

#include "parser/library_map.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

struct TempLibMapDir {
  fs::path dir;

  TempLibMapDir() {
    static std::atomic<uint64_t> counter{0};
    auto seq = counter.fetch_add(1);
    dir = fs::temp_directory_path() /
          ("delta_libmap_" + std::to_string(::getpid()) + "_" +
           std::to_string(seq));
    fs::create_directories(dir);
    // The loader canonicalizes the map file's directory when anchoring relative
    // paths, so canonicalize here too (e.g. macOS resolves /var ->
    // /private/var) to keep the paths we assert on aligned with the loader's
    // view.
    dir = fs::weakly_canonical(dir);
  }

  ~TempLibMapDir() {
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

TEST(LibraryMapInclude, LoadsLibraryDeclarationFromMapFile) {
  TempLibMapDir tmp;
  auto top = tmp.Write("lib.map", "library rtlLib *.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "rtlLib");
}

TEST(LibraryMapInclude, IncludeMergesReferencedFile) {
  TempLibMapDir tmp;
  tmp.Write("sub.map", "library subLib *.sv;\n");
  auto top = tmp.Write("top.map",
                       "library topLib *.v;\n"
                       "include sub.map;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.v").string()), "topLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "y.sv").string()), "subLib");
}

TEST(LibraryMapInclude, RelativeIncludePathAnchorsToContainingFile) {
  TempLibMapDir tmp;
  auto sub_dir = tmp.dir / "subdir";
  fs::create_directories(sub_dir);
  tmp.Write("subdir/sub.map", "library subLib *.sv;\n");
  auto top = tmp.Write("top.map", "include subdir/sub.map;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((sub_dir / "x.sv").string()), "subLib");
}

TEST(LibraryMapInclude, RelativeLibrarySpecAnchorsToContainingFile) {
  TempLibMapDir tmp;
  auto a_dir = tmp.dir / "a";
  fs::create_directories(a_dir);
  tmp.Write("a/sub.map", "library inner *.v;\n");
  auto top = tmp.Write("top.map", "include a/sub.map;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));

  EXPECT_EQ(m.LibraryForFile((a_dir / "x.v").string()), "inner");

  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.v").string()), "work");
}

TEST(LibraryMapInclude, NestedIncludesAccumulateAllDeclarations) {
  TempLibMapDir tmp;
  tmp.Write("c.map", "library cLib *.cv;\n");
  tmp.Write("b.map",
            "include c.map;\n"
            "library bLib *.bv;\n");
  auto top = tmp.Write("a.map",
                       "include b.map;\n"
                       "library aLib *.av;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.av").string()), "aLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.bv").string()), "bLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.cv").string()), "cLib");
}

TEST(LibraryMapInclude, CycleIsDetectedAndReported) {
  TempLibMapDir tmp;
  tmp.Write("a.map", "include b.map;\n");
  auto top = tmp.Write("b.map", "include a.map;\n");
  LibraryMap m;
  std::vector<std::string> errors;
  EXPECT_FALSE(m.LoadMapFile(top, &errors));
  EXPECT_FALSE(errors.empty());
}

TEST(LibraryMapInclude, MissingIncludeIsReported) {
  TempLibMapDir tmp;
  auto top = tmp.Write("top.map", "include nonexistent.map;\n");
  LibraryMap m;
  std::vector<std::string> errors;
  EXPECT_FALSE(m.LoadMapFile(top, &errors));
  EXPECT_FALSE(errors.empty());
}

// A relative include path is resolved against the map file that physically
// contains it, at every level of nesting -- not against the root map's
// directory. Here the second-level map lives in a subdirectory and pulls in a
// sibling by a bare relative name; that name only resolves if anchoring tracks
// the immediate containing file.
TEST(LibraryMapInclude, NestedRelativeIncludeAnchorsToImmediateContainingFile) {
  TempLibMapDir tmp;
  auto sub_dir = tmp.dir / "sub";
  fs::create_directories(sub_dir);
  tmp.Write("sub/b.map", "library deep *.dv;\n");
  tmp.Write("sub/a.map", "include b.map;\n");
  auto top = tmp.Write("top.map", "include sub/a.map;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((sub_dir / "x.dv").string()), "deep");
}

// A lib.map's permitted content is limited to library specifications, include
// statements, and standard SystemVerilog comment syntax. Here line and block
// comments are interleaved with a library declaration and an include; the
// loader must consume them via the ordinary lexer and still resolve both the
// local and the included library, confirming comments are an accepted form.
TEST(LibraryMapInclude, StandardCommentSyntaxIsAcceptedInMapFile) {
  TempLibMapDir tmp;
  tmp.Write("sub.map",
            "// leading line comment in the included map\n"
            "library subLib *.sv;\n");
  auto top = tmp.Write("top.map",
                       "// top-level line comment\n"
                       "library topLib *.v; /* trailing block comment */\n"
                       "/* multi-line block\n"
                       "   comment before the include */\n"
                       "include sub.map;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.v").string()), "topLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "y.sv").string()), "subLib");
}

// The permitted content of a lib.map is limited to library specifications,
// include statements, and comments. A construct outside that set -- here an
// ordinary module declaration -- is therefore not accepted and the load fails
// with a diagnostic, confirming the "limited to" constraint is enforced rather
// than silently tolerated.
TEST(LibraryMapInclude, NonPermittedConstructInMapFileIsRejected) {
  TempLibMapDir tmp;
  auto top = tmp.Write("top.map", "module m; endmodule\n");
  LibraryMap m;
  std::vector<std::string> errors;
  EXPECT_FALSE(m.LoadMapFile(top, &errors));
  EXPECT_FALSE(errors.empty());
}

// An absolute include path is honored as given; the containing-file anchoring
// rule applies only to relative paths.
TEST(LibraryMapInclude, AbsoluteIncludePathIsHonoredAsGiven) {
  TempLibMapDir tmp;
  auto away_dir = tmp.dir / "elsewhere";
  fs::create_directories(away_dir);
  auto away = tmp.Write("elsewhere/abs.map", "library absLib *.av;\n");
  auto top = tmp.Write("top.map", "include " + away.string() + ";\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((away_dir / "x.av").string()), "absLib");
}

}  // namespace
