#include <gtest/gtest.h>

#include <string_view>

#include "parser/ast.h"
#include "parser/library_map.h"

using namespace delta;

namespace {

// §33.8.3 fixture: four library declarations, three of which can match
// the same file_path_spec for some of the example sources.  All four
// share the same base directory because, in the example, evaluation is
// performed from /proj/tb — the absolute specs ignore the base while
// the lib3 relative spec ("../lib/") anchors to it.
LibraryMap MakeFixture() {
  LibraryMap m;

  LibraryDecl lib1;
  lib1.name = "lib1";
  lib1.file_paths.push_back("/proj/lib/foo*.v");
  m.AddDeclaration(lib1, "/proj/tb");

  LibraryDecl lib2;
  lib2.name = "lib2";
  lib2.file_paths.push_back("/proj/lib/foo.v");
  m.AddDeclaration(lib2, "/proj/tb");

  LibraryDecl lib3;
  lib3.name = "lib3";
  lib3.file_paths.push_back("../lib/");
  m.AddDeclaration(lib3, "/proj/tb");

  LibraryDecl lib4;
  lib4.name = "lib4";
  lib4.file_paths.push_back("/proj/lib/*ver.v");
  m.AddDeclaration(lib4, "/proj/tb");

  return m;
}

// §33.8.3 row 1: foobar.v is matched by lib1's "foo*.v" wildcard
// filename and by lib3's directory-only spec.  Per §33.3.1.1 b, the
// filename-bearing spec outranks the directory-only spec, so the
// resolver must pick lib1.
TEST(LibraryMapMultipleSpecExample, FoobarPicksLib1OverLib3) {
  EXPECT_EQ(MakeFixture().LibraryForFile("/proj/lib/foobar.v"), "lib1");
}

// §33.8.3 row 2: foo.v is matched by lib2 (explicit filename), lib1
// (wildcard filename), and lib3 (directory).  Per §33.3.1.1 a, the
// explicit-filename spec wins outright over both lower-priority tiers.
TEST(LibraryMapMultipleSpecExample, FooPicksLib2OverLib1AndLib3) {
  EXPECT_EQ(MakeFixture().LibraryForFile("/proj/lib/foo.v"), "lib2");
}

// §33.8.3 row 3: bar.v is matched only by lib3's directory spec — the
// other three filename-bearing specs all reject it.  Per §33.3.1.1 c,
// the directory-only match still resolves the file when no
// higher-priority spec applies.
TEST(LibraryMapMultipleSpecExample, BarPicksLib3) {
  EXPECT_EQ(MakeFixture().LibraryForFile("/proj/lib/bar.v"), "lib3");
}

// §33.8.3 row 4: barver.v is matched by lib4's "*ver.v" wildcard
// filename and by lib3's directory spec.  Per §33.3.1.1 b, the
// filename-bearing spec outranks the directory-only spec, so the
// resolver must pick lib4.
TEST(LibraryMapMultipleSpecExample, BarverPicksLib4OverLib3) {
  EXPECT_EQ(MakeFixture().LibraryForFile("/proj/lib/barver.v"), "lib4");
}

// §33.8.3 row 5: foover.v is matched by both lib1's "foo*.v" and
// lib4's "*ver.v" — two different libraries at the same
// wildcard-filename priority tier.  This is the ambiguity case from
// §33.3.1.1; the resolver must surface it as an error rather than
// silently choosing one library, which we observe as the empty-string
// sentinel.
TEST(LibraryMapMultipleSpecExample, FooverIsAmbiguousAcrossLib1AndLib4) {
  EXPECT_EQ(MakeFixture().LibraryForFile("/proj/lib/foover.v"), "");
}

// §33.8.3 row 6: tb.v under /test/tb is not matched by any of the four
// specs (lib3's directory anchors at /proj/lib, the others are pinned
// to /proj/lib outright).  Per §33.3.1, files that match no library
// specification map into the special library `work`.
TEST(LibraryMapMultipleSpecExample, UnmatchedTbFileMapsToWork) {
  EXPECT_EQ(MakeFixture().LibraryForFile("/test/tb/tb.v"), "work");
}

}  // namespace
