#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

// --- §5.6: Identifiers, keywords, and system names ---

TEST(LexerCh506, IdentifierMaxLengthError) {
  // §5.6: Limit shall be at least 1024; error if exceeded.
  std::string id(1025, 'a');
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", id);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}

TEST(LexerCh506, EscapedIdentifierMaxLengthError) {
  // §5.6: Length limit applies to escaped identifiers too.
  std::string id = "\\" + std::string(1025, 'a') + " ";
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", id);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}
struct ParseResult31201 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult31201 Parse(const std::string &src) {
  ParseResult31201 result;
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

static const ModuleItem *FindItemByKindAndName(
    const std::vector<ModuleItem *> &items, ModuleItemKind kind,
    const std::string &name) {
  for (const auto *item : items)
    if (item->kind == kind && item->name == name) return item;
  return nullptr;
}

// 9. $unit:: scope resolution operator — used for disambiguation.
// $unit is lexed as a system identifier; $unit::name is the syntax.
TEST(ParserClause03, Cl3_12_1_DollarUnitScopeResolution) {
  // The LRM example: b = 5 + $unit::b;
  // $unit is a kSystemIdentifier token; :: is kColonColon.
  // This tests that the lexer correctly produces these tokens.
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "$unit::b");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto t1 = lexer.Next();
  EXPECT_EQ(t1.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(t1.text, "$unit");
  auto t2 = lexer.Next();
  EXPECT_EQ(t2.kind, TokenKind::kColonColon);
  auto t3 = lexer.Next();
  EXPECT_EQ(t3.kind, TokenKind::kIdentifier);
  EXPECT_EQ(t3.text, "b");
}

