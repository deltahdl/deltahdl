#include <gtest/gtest.h>

#include <string_view>

#include "parser/ast.h"
#include "parser/library_map.h"

using namespace delta;

namespace {

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

TEST(LibraryMapMultipleSpecExample, FoobarPicksLib1OverLib3) {
  EXPECT_EQ(MakeFixture().LibraryForFile("/proj/lib/foobar.v"), "lib1");
}

TEST(LibraryMapMultipleSpecExample, FooPicksLib2OverLib1AndLib3) {
  EXPECT_EQ(MakeFixture().LibraryForFile("/proj/lib/foo.v"), "lib2");
}

TEST(LibraryMapMultipleSpecExample, BarPicksLib3) {
  EXPECT_EQ(MakeFixture().LibraryForFile("/proj/lib/bar.v"), "lib3");
}

TEST(LibraryMapMultipleSpecExample, BarverPicksLib4OverLib3) {
  EXPECT_EQ(MakeFixture().LibraryForFile("/proj/lib/barver.v"), "lib4");
}

TEST(LibraryMapMultipleSpecExample, FooverIsAmbiguousAcrossLib1AndLib4) {
  EXPECT_EQ(MakeFixture().LibraryForFile("/proj/lib/foover.v"), "");
}

TEST(LibraryMapMultipleSpecExample, UnmatchedTbFileMapsToWork) {
  EXPECT_EQ(MakeFixture().LibraryForFile("/test/tb/tb.v"), "work");
}

}
