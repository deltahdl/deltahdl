#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

struct FilePathResult {
  SourceManager mgr;
  Token token;
  bool has_errors;
};

inline FilePathResult LexFilePathSpec(const std::string& src) {
  FilePathResult r;
  DiagEngine diag(r.mgr);
  auto fid = r.mgr.AddFile("<test>", src);
  Lexer lexer(r.mgr.FileContent(fid), fid, diag);
  r.token = lexer.NextFilePathSpec();
  r.has_errors = diag.HasErrors();
  return r;
}

// --- file_path_spec basic paths ---

TEST(FilePathSpecLexing, SimpleFilename) {
  auto r = LexFilePathSpec("file.v");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, "file.v");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, AbsolutePath) {
  auto r = LexFilePathSpec("/proj/rtl/top.v");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, "/proj/rtl/top.v");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, RelativeDotSlash) {
  auto r = LexFilePathSpec("./dir/file.v");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, "./dir/file.v");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, RelativeParentDir) {
  auto r = LexFilePathSpec("../rtl/file.v");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, "../rtl/file.v");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, WildcardStar) {
  auto r = LexFilePathSpec("*.v");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, "*.v");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, WildcardQuestion) {
  auto r = LexFilePathSpec("?.v");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, "?.v");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, HierarchicalWildcard) {
  auto r = LexFilePathSpec(".../file.v");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, ".../file.v");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, DirectoryTrailingSlash) {
  auto r = LexFilePathSpec("/proj/rtl/");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, "/proj/rtl/");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, MultipleDots) {
  auto r = LexFilePathSpec("file.name.ext.v");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, "file.name.ext.v");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, QuotedPath) {
  auto r = LexFilePathSpec("\"file.v\"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, "\"file.v\"");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, EnvironmentVariable) {
  auto r = LexFilePathSpec("$PROJ/rtl/*.v");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, "$PROJ/rtl/*.v");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, TildePath) {
  auto r = LexFilePathSpec("~/proj/file.v");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(r.token.text, "~/proj/file.v");
  EXPECT_FALSE(r.has_errors);
}

// --- Delimiter handling ---

TEST(FilePathSpecLexing, StopsAtSpace) {
  auto r = LexFilePathSpec("path.v rest");
  EXPECT_EQ(r.token.text, "path.v");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, StopsAtTab) {
  auto r = LexFilePathSpec("path.v\trest");
  EXPECT_EQ(r.token.text, "path.v");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, StopsAtNewline) {
  auto r = LexFilePathSpec("path.v\nrest");
  EXPECT_EQ(r.token.text, "path.v");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, StopsAtComma) {
  auto r = LexFilePathSpec("path.v,rest");
  EXPECT_EQ(r.token.text, "path.v");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, StopsAtSemicolon) {
  auto r = LexFilePathSpec("path.v;");
  EXPECT_EQ(r.token.text, "path.v");
  EXPECT_FALSE(r.has_errors);
}

// --- Whitespace and comment skipping ---

TEST(FilePathSpecLexing, SkipsLeadingSpaces) {
  auto r = LexFilePathSpec("   path.v");
  EXPECT_EQ(r.token.text, "path.v");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, SkipsLeadingLineComment) {
  auto r = LexFilePathSpec("// comment\npath.v");
  EXPECT_EQ(r.token.text, "path.v");
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, SkipsLeadingBlockComment) {
  auto r = LexFilePathSpec("/* comment */path.v");
  EXPECT_EQ(r.token.text, "path.v");
  EXPECT_FALSE(r.has_errors);
}

// --- Source location ---

TEST(FilePathSpecLexing, SourceLocationAtStart) {
  auto r = LexFilePathSpec("path.v");
  EXPECT_EQ(r.token.loc.line, 1u);
  EXPECT_EQ(r.token.loc.column, 1u);
}

TEST(FilePathSpecLexing, SourceLocationAfterWhitespace) {
  auto r = LexFilePathSpec("  path.v");
  EXPECT_EQ(r.token.loc.line, 1u);
  EXPECT_EQ(r.token.loc.column, 3u);
}

TEST(FilePathSpecLexing, SourceLocationAfterComment) {
  auto r = LexFilePathSpec("// comment\npath.v");
  EXPECT_EQ(r.token.loc.line, 2u);
  EXPECT_EQ(r.token.loc.column, 1u);
}

// --- Empty/EOF ---

TEST(FilePathSpecLexing, EmptyInput) {
  auto r = LexFilePathSpec("");
  EXPECT_EQ(r.token.kind, TokenKind::kEof);
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, WhitespaceOnly) {
  auto r = LexFilePathSpec("   ");
  EXPECT_EQ(r.token.kind, TokenKind::kEof);
  EXPECT_FALSE(r.has_errors);
}

TEST(FilePathSpecLexing, CommentOnly) {
  auto r = LexFilePathSpec("// just a comment\n");
  EXPECT_EQ(r.token.kind, TokenKind::kEof);
  EXPECT_FALSE(r.has_errors);
}

// --- Error conditions ---

TEST(FilePathSpecLexing, ErrorCommaImmediate) {
  auto r = LexFilePathSpec(",rest");
  EXPECT_EQ(r.token.kind, TokenKind::kEof);
  EXPECT_TRUE(r.has_errors);
}

TEST(FilePathSpecLexing, ErrorSemicolonImmediate) {
  auto r = LexFilePathSpec(";");
  EXPECT_EQ(r.token.kind, TokenKind::kEof);
  EXPECT_TRUE(r.has_errors);
}

// --- Consecutive calls ---

TEST(FilePathSpecLexing, ConsecutiveCallsSeparatedByWhitespace) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  std::string src = "path1 path2";
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tok1 = lexer.NextFilePathSpec();
  auto tok2 = lexer.NextFilePathSpec();
  EXPECT_EQ(tok1.text, "path1");
  EXPECT_EQ(tok2.text, "path2");
  EXPECT_FALSE(diag.HasErrors());
}

TEST(FilePathSpecLexing, ConsecutiveCallsWithEof) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  std::string src = "only_path";
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tok1 = lexer.NextFilePathSpec();
  auto tok2 = lexer.NextFilePathSpec();
  EXPECT_EQ(tok1.kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tok1.text, "only_path");
  EXPECT_EQ(tok2.kind, TokenKind::kEof);
}

}  // namespace
