// §33.3: Libraries

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

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

// =============================================================================
// A.1.1 library_text ::= { library_description }
// =============================================================================
// Empty library text produces an empty CompilationUnit.
TEST(LibraryText, EmptyInput) {
  auto r = ParseLibrary("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->libraries.empty());
  EXPECT_TRUE(r.cu->lib_includes.empty());
  EXPECT_TRUE(r.cu->configs.empty());
}

// A null library description (bare semicolon) is valid.
TEST(LibraryText, NullDescription) {
  auto r = ParseLibrary(";\n;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->libraries.empty());
}

// =============================================================================
// A.1.1 library_declaration ::=
//   library library_identifier file_path_spec
//   { , file_path_spec } [ -incdir file_path_spec { , file_path_spec } ] ;
// =============================================================================
// Basic library declaration with a single file path.
TEST(LibraryText, BasicLibraryDecl) {
  auto r = ParseLibrary("library mylib /proj/rtl/top.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "mylib");
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/rtl/top.v");
}

// Library declaration with wildcard file path.
TEST(LibraryText, LibraryDeclWildcard) {
  auto r = ParseLibrary("library rtlLib *.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "rtlLib");
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "*.v");
}

// Library declaration with dot-slash relative path.
TEST(LibraryText, LibraryDeclDotSlash) {
  auto r = ParseLibrary("library gateLib ./*.vg;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "./*.vg");
}

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

// =============================================================================
// A.1.1 include_statement ::= include file_path_spec ;
// =============================================================================
// Basic include statement.
TEST(LibraryText, IncludeStatement) {
  auto r = ParseLibrary("include /proj/other.map;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->lib_includes.size(), 1u);
  EXPECT_EQ(r.cu->lib_includes[0]->file_path, "/proj/other.map");
}

// Include statement with relative path.
TEST(LibraryText, IncludeStatementRelative) {
  auto r = ParseLibrary("include ./sub/lib.map;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->lib_includes.size(), 1u);
  EXPECT_EQ(r.cu->lib_includes[0]->file_path, "./sub/lib.map");
}

// =============================================================================
// A.1.1 library_description ::=
//   library_declaration | include_statement | config_declaration | ;
// =============================================================================
// Multiple library descriptions mixed together.
TEST(LibraryText, MixedDescriptions) {
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

// =============================================================================
// Comments in library source text.
// =============================================================================
// Line comments.
TEST(LibraryText, LineComments) {
  auto r = ParseLibrary(
      "// This is a library map file\n"
      "library lib1 /proj/*.v; // RTL files\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
}

// Block comments.
TEST(LibraryText, BlockComments) {
  auto r = ParseLibrary(
      "/* Multi-line\n"
      "   comment */\n"
      "library lib1 /proj/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
}

// =============================================================================
// AST structural verification — ensures AST nodes capture all data.
// =============================================================================
// Verify LibraryDecl stores source range.
TEST(LibraryText, LibraryDeclHasSourceRange) {
  auto r = ParseLibrary("library mylib /proj/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_NE(r.cu->libraries[0]->range.start.line, 0u);
}

// Verify IncludeStmt stores source location.
TEST(LibraryText, IncludeStmtHasSourceLoc) {
  auto r = ParseLibrary("include /proj/lib.map;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->lib_includes.size(), 1u);
  EXPECT_NE(r.cu->lib_includes[0]->loc.line, 0u);
}

// =============================================================================
// Multiple library declarations.
// =============================================================================
// Multiple libraries, each mapping different file patterns.
TEST(LibraryText, MultipleLibraries) {
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

// =============================================================================
// Error handling.
// =============================================================================
// Missing semicolon after library declaration.
TEST(LibraryText, ErrorMissingSemicolon) {
  auto r = ParseLibrary("library lib /proj/*.v\n");
  EXPECT_TRUE(r.has_errors);
}

// Missing file path spec.
TEST(LibraryText, ErrorMissingFilePath) {
  auto r = ParseLibrary("library lib;\n");
  // Should produce an error: file_path_spec is required.
  EXPECT_TRUE(r.has_errors);
}

// Missing library identifier.
TEST(LibraryText, ErrorMissingLibraryName) {
  auto r = ParseLibrary("library;\n");
  EXPECT_TRUE(r.has_errors);
}

// Include without file path.
TEST(LibraryText, ErrorIncludeNoPath) {
  auto r = ParseLibrary("include;\n");
  EXPECT_TRUE(r.has_errors);
}

// =============================================================================
// LRM §33 examples — library map file from the specification.
// =============================================================================
// LRM example: library rtlLib *.v;
TEST(LibraryText, LrmExampleSimple) {
  auto r = ParseLibrary("library rtlLib *.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "rtlLib");
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "*.v");
}

// LRM example: library gateLib ./*.vg;
TEST(LibraryText, LrmExampleDotSlash) {
  auto r = ParseLibrary("library gateLib ./*.vg;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "gateLib");
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "./*.vg");
}

// LRM comprehensive example with all features.
TEST(LibraryText, LrmComprehensiveExample) {
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

// =============================================================================
// Lexer: file_path_spec token recognition.
// =============================================================================
// Verify the lexer correctly reads file path specs with special chars.
TEST(LibraryText, LexerFilePathSpecAbsolute) {
  auto r = ParseLibrary("library lib /proj/rtl/top.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/rtl/top.v");
}

// File path spec with parent directory (..).
TEST(LibraryText, LexerFilePathSpecParentDir) {
  auto r = ParseLibrary("library lib ../rtl/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "../rtl/*.v");
}

}  // namespace
