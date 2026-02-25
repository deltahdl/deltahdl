// §3.14: Simulation time units and precision

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

static LexResult LexOne(const std::string& src) {
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
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult314 Parse(const std::string& src) {
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

static bool ParseOk(const std::string& src) {
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

// 11. DelayToTicks covers the full range from seconds to femtoseconds.
TEST(ParserClause03, Cl3_14_DelayToTicksFullRange) {
  // 1 second at fs precision = 10^15 ticks.
  TimeScale ts_s{TimeUnit::kS, 1, TimeUnit::kFs, 1};
  EXPECT_EQ(DelayToTicks(1, ts_s, TimeUnit::kFs), 1000000000000000ULL);
  // 1 fs at fs precision = 1 tick.
  TimeScale ts_fs{TimeUnit::kFs, 1, TimeUnit::kFs, 1};
  EXPECT_EQ(DelayToTicks(1, ts_fs, TimeUnit::kFs), 1u);
}

}  // namespace
