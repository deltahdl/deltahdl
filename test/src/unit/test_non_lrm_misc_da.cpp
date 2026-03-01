// Non-LRM tests

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using ConfigParseTest = ProgramTestParse;

ParseResult ParseLibrary(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.ParseLibraryText();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// Library declaration with multiple file paths.
TEST(LibraryText, LibraryDeclMultiplePaths) {
  auto r = ParseLibrary("library lib /a/*.v, /b/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 2u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/a/*.v");
  EXPECT_EQ(r.cu->libraries[0]->file_paths[1], "/b/*.v");
}

// Library declaration with -incdir clause.
TEST(LibraryText, LibraryDeclWithIncdir) {
  auto r = ParseLibrary("library lib /proj/*.v -incdir /proj/inc;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/*.v");
  ASSERT_EQ(r.cu->libraries[0]->incdir_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[0], "/proj/inc");
}

// Library declaration with multiple -incdir paths.
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

// Library declaration with both multiple file paths and multiple -incdir.
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

// Library declaration with hierarchical wildcard path (...).
TEST(LibraryText, LibraryDeclHierarchicalWildcard) {
  auto r = ParseLibrary("library deepLib .../a.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], ".../a.v");
}

// Library declaration with single-char wildcard (?).
TEST(LibraryText, LibraryDeclQuestionWildcard) {
  auto r = ParseLibrary("library lib ./rtl/?.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "./rtl/?.v");
}

// Library declaration with directory-only path (trailing slash).
TEST(LibraryText, LibraryDeclDirectoryPath) {
  auto r = ParseLibrary("library lib /proj/rtl/;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/rtl/");
}

}  // namespace
