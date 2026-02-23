// §5.8: Time literals

#include <gtest/gtest.h>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Helper: lex a single token from source text.
// Returns both the SourceManager (owning the source buffer) and the token
// so that token.text (a string_view) remains valid.
struct LexResult {
  SourceManager mgr;
  Token token;
};

static LexResult LexOne(const std::string &src) {
  LexResult result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  result.token = lexer.Next();
  return result;
}

// Helper: parse source and return the compilation unit.
struct ParseResult314 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult314 Parse(const std::string &src) {
  ParseResult314 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

namespace {

// 7. Lexer: all six time suffixes produce kTimeLiteral tokens.
TEST(ParserClause03, Cl3_14_LexerAllTimeSuffixes) {
  auto r_s = LexOne("1s");
  EXPECT_EQ(r_s.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_s.token.text, "1s");
  auto r_ms = LexOne("1ms");
  EXPECT_EQ(r_ms.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_ms.token.text, "1ms");
  auto r_us = LexOne("1us");
  EXPECT_EQ(r_us.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_us.token.text, "1us");
  auto r_ns = LexOne("1ns");
  EXPECT_EQ(r_ns.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_ns.token.text, "1ns");
  auto r_ps = LexOne("1ps");
  EXPECT_EQ(r_ps.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_ps.token.text, "1ps");
  auto r_fs = LexOne("1fs");
  EXPECT_EQ(r_fs.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_fs.token.text, "1fs");
}

// 8. Lexer: magnitudes 1, 10, 100 with time suffix.
TEST(ParserClause03, Cl3_14_LexerTimeMagnitudes) {
  auto r1 = LexOne("1ns");
  EXPECT_EQ(r1.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r1.token.text, "1ns");
  auto r10 = LexOne("10ns");
  EXPECT_EQ(r10.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r10.token.text, "10ns");
  auto r100 = LexOne("100ns");
  EXPECT_EQ(r100.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r100.token.text, "100ns");
}

}  // namespace
