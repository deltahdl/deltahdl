#include "fixture_parser.h"

using namespace delta;

namespace {

// --- library_text ::= { library_description } ---

TEST(LibraryText, EmptyInput) {
  auto r = ParseLibrary("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->libraries.empty());
  EXPECT_TRUE(r.cu->lib_includes.empty());
  EXPECT_TRUE(r.cu->configs.empty());
}

TEST(LibraryText, NullDescription) {
  auto r = ParseLibrary(";\n;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->libraries.empty());
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

TEST(LibraryText, MixedDescriptionsUnquotedPaths) {
  auto r = ParseLibrary(
      "library lib1 /a/*.v;\n"
      ";\n"
      "include /proj/other.map;\n"
      "library lib2 /b/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 2u);
  EXPECT_EQ(r.cu->libraries[0]->name, "lib1");
  EXPECT_EQ(r.cu->libraries[1]->name, "lib2");
  ASSERT_EQ(r.cu->lib_includes.size(), 1u);
}

TEST(LibraryText, ComprehensiveExample) {
  auto r = ParseLibrary(
      "// Library map file\n"
      "library rtlLib /proj/rtl/*.v, /proj/common/*.v\n"
      "  -incdir /proj/inc, /proj/common/inc;\n"
      "library gateLib /proj/gates/*.vg;\n"
      "include /proj/sub_libs.map;\n"
      "config top_cfg;\n"
      "  design rtlLib.top;\n"
      "  default liblist rtlLib gateLib;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 2u);
  ASSERT_EQ(r.cu->lib_includes.size(), 1u);
  ASSERT_EQ(r.cu->configs.size(), 1u);
}

TEST(LibraryText, ErrorUnexpectedToken) {
  auto r = ParseLibrary("module m; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LibraryText, LineComments) {
  auto r = ParseLibrary(
      "// This is a library map file\n"
      "library lib1 /proj/*.v; // RTL files\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
}

TEST(LibraryText, BlockComments) {
  auto r = ParseLibrary(
      "/* Multi-line\n"
      "   comment */\n"
      "library lib1 /proj/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
}

TEST(LibraryText, CommentsOnlyInput) {
  auto r = ParseLibrary(
      "// line comment\n"
      "/* block comment */\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->libraries.empty());
  EXPECT_TRUE(r.cu->lib_includes.empty());
  EXPECT_TRUE(r.cu->configs.empty());
}

// --- library_description ::= config_declaration ---

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

TEST(LibraryText, ConfigWithLibraryDecl) {
  auto r = ParseLibrary(
      "library lib1 /a/*.v;\n"
      "config cfg;\n"
      "  design lib1.top;\n"
      "  default liblist lib1;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

// --- library_declaration ---

TEST(LibraryText, SingleLibraryDecl) {
  auto r = ParseLibrary("library mylib \"file.sv\";\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "mylib");
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_TRUE(r.cu->libraries[0]->incdir_paths.empty());
}

TEST(LibraryText, BasicLibraryDecl) {
  auto r = ParseLibrary("library mylib /proj/rtl/top.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "mylib");
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/rtl/top.v");
}

TEST(LibraryText, BasicLibraryDeclQuotedPath) {
  auto r = ParseLibrary("library work \"*.sv\";\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "work");
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

TEST(LibraryText, LibraryDeclMultiplePaths) {
  auto r = ParseLibrary("library lib /a/*.v, /b/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 2u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/a/*.v");
  EXPECT_EQ(r.cu->libraries[0]->file_paths[1], "/b/*.v");
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

TEST(LibraryText, ThreeLibraryDecls) {
  auto r = ParseLibrary(
      "library rtlLib *.v;\n"
      "library gateLib ./*.vg;\n"
      "library tbLib ../tb/*.sv;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 3u);
  EXPECT_EQ(r.cu->libraries[0]->name, "rtlLib");
  EXPECT_EQ(r.cu->libraries[1]->name, "gateLib");
  EXPECT_EQ(r.cu->libraries[2]->name, "tbLib");
}

TEST(LibraryText, LibraryDeclHasSourceRange) {
  auto r = ParseLibrary("library mylib /proj/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_NE(r.cu->libraries[0]->range.start.line, 0u);
}

// --- library_declaration -incdir clause ---

TEST(LibraryText, LibraryDeclWithIncdir) {
  auto r =
      ParseLibrary("library mylib \"rtl/*.sv\" -incdir \"inc1\", \"inc2\";\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths.size(), 2u);
}

TEST(LibraryText, LibraryDeclSingleIncdir) {
  auto r = ParseLibrary("library lib /proj/*.v -incdir /proj/inc;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/*.v");
  ASSERT_EQ(r.cu->libraries[0]->incdir_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[0], "/proj/inc");
}

TEST(LibraryText, LibraryDeclMultipleIncdir) {
  auto r = ParseLibrary("library lib /proj/*.v -incdir /inc1, /inc2, /inc3;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  ASSERT_EQ(r.cu->libraries[0]->incdir_paths.size(), 3u);
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[0], "/inc1");
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[1], "/inc2");
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[2], "/inc3");
}

TEST(LibraryText, LibraryDeclFullForm) {
  auto r = ParseLibrary(
      "library rtlLib /proj/rtl/*.v, /proj/extra/*.v\n"
      "  -incdir /proj/inc, /proj/common;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "rtlLib");
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 2u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/rtl/*.v");
  EXPECT_EQ(r.cu->libraries[0]->file_paths[1], "/proj/extra/*.v");
  ASSERT_EQ(r.cu->libraries[0]->incdir_paths.size(), 2u);
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[0], "/proj/inc");
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[1], "/proj/common");
}

// --- file_path_spec variants ---

TEST(LibraryText, FilePathSpecWildcard) {
  auto r = ParseLibrary("library rtlLib *.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "rtlLib");
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "*.v");
}

TEST(LibraryText, FilePathSpecDotSlash) {
  auto r = ParseLibrary("library gateLib ./*.vg;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "./*.vg");
}

TEST(LibraryText, FilePathSpecAbsolute) {
  auto r = ParseLibrary("library lib /proj/rtl/top.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/rtl/top.v");
}

TEST(LibraryText, FilePathSpecParentDir) {
  auto r = ParseLibrary("library lib ../rtl/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "../rtl/*.v");
}

TEST(LibraryText, FilePathSpecHierarchicalWildcard) {
  auto r = ParseLibrary("library deepLib .../a.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], ".../a.v");
}

TEST(LibraryText, FilePathSpecQuestionWildcard) {
  auto r = ParseLibrary("library lib ./rtl/?.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "./rtl/?.v");
}

TEST(LibraryText, FilePathSpecDirectoryPath) {
  auto r = ParseLibrary("library lib /proj/rtl/;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/rtl/");
}

TEST(LibraryText, QuotedFilePathValue) {
  auto r = ParseLibrary("library lib \"src/*.sv\";\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "\"src/*.sv\"");
}

// --- include_statement ---

TEST(LibraryText, IncludeStatement) {
  auto r = ParseLibrary("include \"extra.svlib\";\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->lib_includes.size(), 1u);
}

TEST(LibraryText, IncludeStatementAbsolute) {
  auto r = ParseLibrary("include /proj/other.map;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->lib_includes.size(), 1u);
  EXPECT_EQ(r.cu->lib_includes[0]->file_path, "/proj/other.map");
}

TEST(LibraryText, IncludeStatementRelative) {
  auto r = ParseLibrary("include ./sub/lib.map;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->lib_includes.size(), 1u);
  EXPECT_EQ(r.cu->lib_includes[0]->file_path, "./sub/lib.map");
}

TEST(LibraryText, IncludeStmtHasSourceLoc) {
  auto r = ParseLibrary("include /proj/lib.map;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->lib_includes.size(), 1u);
  EXPECT_NE(r.cu->lib_includes[0]->loc.line, 0u);
}

TEST(LibraryText, MultipleIncludeStatements) {
  auto r = ParseLibrary(
      "include /proj/a.map;\n"
      "include /proj/b.map;\n"
      "include /proj/c.map;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->lib_includes.size(), 3u);
  EXPECT_EQ(r.cu->lib_includes[0]->file_path, "/proj/a.map");
  EXPECT_EQ(r.cu->lib_includes[1]->file_path, "/proj/b.map");
  EXPECT_EQ(r.cu->lib_includes[2]->file_path, "/proj/c.map");
}

// --- Error conditions ---

TEST(LibraryText, ErrorMissingSemicolon) {
  auto r = ParseLibrary("library lib /proj/*.v\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LibraryText, ErrorMissingFilePath) {
  auto r = ParseLibrary("library lib;\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LibraryText, ErrorMissingLibraryName) {
  auto r = ParseLibrary("library;\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LibraryText, ErrorIncludeNoPath) {
  auto r = ParseLibrary("include;\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LibraryText, ErrorIncludeMissingSemicolon) {
  auto r = ParseLibrary("include /proj/lib.map\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LibraryText, ErrorTrailingCommaInFileList) {
  auto r = ParseLibrary("library lib /a.v, ;\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
