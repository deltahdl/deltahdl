#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(LibraryText, NullDescription) {
  auto r = ParseLibrary(";\n;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->libraries.empty());
}

TEST(LibraryText, EmptyInput) {
  auto r = ParseLibrary("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->libraries.empty());
  EXPECT_TRUE(r.cu->lib_includes.empty());
  EXPECT_TRUE(r.cu->configs.empty());
}

TEST(LibraryText, SingleLibraryDecl) {
  auto r = ParseLibrary("library mylib \"file.sv\";\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "mylib");
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_TRUE(r.cu->libraries[0]->incdir_paths.empty());
}

TEST(LibraryText, LibraryDeclMultipleFiles) {
  auto r =
      ParseLibrary("library work \"src/a.sv\", \"src/b.sv\", \"src/c.sv\";\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "work");
  EXPECT_EQ(r.cu->libraries[0]->file_paths.size(), 3u);
}

TEST(LibraryText, LibraryDeclWithIncdir) {
  auto r =
      ParseLibrary("library mylib \"rtl/*.sv\" -incdir \"inc1\", \"inc2\";\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths.size(), 2u);
}

TEST(LibraryText, MultipleLibraryDecls) {
  auto r = ParseLibrary(
      "library work \"work/*.sv\";\n"
      "library rtl  \"rtl/*.sv\";\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 2u);
  EXPECT_EQ(r.cu->libraries[0]->name, "work");
  EXPECT_EQ(r.cu->libraries[1]->name, "rtl");
}

TEST(LibraryText, IncludeStatement) {
  auto r = ParseLibrary("include \"extra.svlib\";\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->lib_includes.size(), 1u);
}

TEST(LibraryText, ConfigInLibraryText) {
  auto r = ParseLibrary(
      "config cfg;\n"
      "  design work.top;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

TEST(LibraryText, MixedDescriptions) {
  auto r = ParseLibrary(
      ";\n"
      "library work \"work/*.sv\";\n"
      "include \"other.svlib\";\n"
      "config cfg;\n"
      "  design work.top;\n"
      "endconfig\n"
      ";\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->lib_includes.size(), 1u);
  EXPECT_EQ(r.cu->configs.size(), 1u);
}

TEST(LibraryText, ErrorUnexpectedToken) {
  auto r = ParseLibrary("module m; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}
