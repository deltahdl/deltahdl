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
