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

// Per-test temp directory under the OS temp area.  Each instance picks
// a fresh directory using pid + a process-local counter so concurrent
// tests do not collide.
struct TempLibMapDir {
  fs::path dir;

  TempLibMapDir() {
    static std::atomic<uint64_t> counter{0};
    auto seq = counter.fetch_add(1);
    dir = fs::temp_directory_path() /
          ("delta_libmap_" + std::to_string(::getpid()) + "_" +
           std::to_string(seq));
    fs::create_directories(dir);
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

// §33.3.2: simplest case — a lib.map's library declaration is loaded.
TEST(LibraryMapInclude, LoadsLibraryDeclarationFromMapFile) {
  TempLibMapDir tmp;
  auto top = tmp.Write("lib.map", "library rtlLib *.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "rtlLib");
}

// §33.3.2 item 1: include inserts the contents of the referenced map.
TEST(LibraryMapInclude, IncludeMergesReferencedFile) {
  TempLibMapDir tmp;
  tmp.Write("sub.map", "library subLib *.sv;\n");
  auto top = tmp.Write("top.map",
                       "library topLib *.v;\n"
                       "include \"sub.map\";\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.v").string()), "topLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "y.sv").string()), "subLib");
}

// §33.3.2 item 2 (include side): a relative include path is resolved
// against the directory of the file that contains it.
TEST(LibraryMapInclude, RelativeIncludePathAnchorsToContainingFile) {
  TempLibMapDir tmp;
  auto sub_dir = tmp.dir / "subdir";
  fs::create_directories(sub_dir);
  tmp.Write("subdir/sub.map", "library subLib *.sv;\n");
  auto top = tmp.Write("top.map", "include \"subdir/sub.map\";\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((sub_dir / "x.sv").string()), "subLib");
}

// §33.3.2 item 2 (library side): a relative library spec inside an
// included file is resolved against that included file's directory.
TEST(LibraryMapInclude, RelativeLibrarySpecAnchorsToContainingFile) {
  TempLibMapDir tmp;
  auto a_dir = tmp.dir / "a";
  fs::create_directories(a_dir);
  tmp.Write("a/sub.map", "library inner *.v;\n");
  auto top = tmp.Write("top.map", "include \"a/sub.map\";\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  // sub.map's "*.v" anchors to a/, so a/x.v should match.
  EXPECT_EQ(m.LibraryForFile((a_dir / "x.v").string()), "inner");
  // The same name in the parent dir should not match — proving the
  // library spec used a/, not the host map's directory.
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.v").string()), "work");
}

// §33.3.2 item 1, transitive: a chain of includes accumulates all
// declarations as if textually inlined.
TEST(LibraryMapInclude, NestedIncludesAccumulateAllDeclarations) {
  TempLibMapDir tmp;
  tmp.Write("c.map", "library cLib *.cv;\n");
  tmp.Write("b.map",
            "include \"c.map\";\n"
            "library bLib *.bv;\n");
  auto top = tmp.Write("a.map",
                       "include \"b.map\";\n"
                       "library aLib *.av;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.av").string()), "aLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.bv").string()), "bLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.cv").string()), "cLib");
}

// §33.3.2 textual-inclusion semantics imply termination — a cycle has
// to be diagnosed instead of silently looping.
TEST(LibraryMapInclude, CycleIsDetectedAndReported) {
  TempLibMapDir tmp;
  tmp.Write("a.map", "include \"b.map\";\n");
  auto top = tmp.Write("b.map", "include \"a.map\";\n");
  LibraryMap m;
  std::vector<std::string> errors;
  EXPECT_FALSE(m.LoadMapFile(top, &errors));
  EXPECT_FALSE(errors.empty());
}

// A missing include target is reported through the error channel
// rather than silently swallowed.
TEST(LibraryMapInclude, MissingIncludeIsReported) {
  TempLibMapDir tmp;
  auto top = tmp.Write("top.map", "include \"nonexistent.map\";\n");
  LibraryMap m;
  std::vector<std::string> errors;
  EXPECT_FALSE(m.LoadMapFile(top, &errors));
  EXPECT_FALSE(errors.empty());
}

}  // namespace
