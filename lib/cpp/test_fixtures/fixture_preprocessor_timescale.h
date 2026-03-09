#pragma once

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct PreprocTimescaleResult {
  SourceManager mgr;
  TimeScale timescale;
  TimeUnit global_precision;
  bool has_timescale;
  bool has_errors;
};

inline PreprocTimescaleResult PreprocessTimescale(const std::string& src) {
  PreprocTimescaleResult result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  preproc.Preprocess(fid);
  result.timescale = preproc.CurrentTimescale();
  result.global_precision = preproc.GlobalPrecision();
  result.has_timescale = preproc.HasTimescale();
  result.has_errors = diag.HasErrors();
  return result;
}

// Alias for tests that use "Preprocess" as a 1-arg call.
inline PreprocTimescaleResult Preprocess(const std::string& src) {
  return PreprocessTimescale(src);
}

struct ParseResult31402 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
  TimeScale preproc_timescale;
  bool has_preproc_timescale = false;
  TimeUnit preproc_global_precision = TimeUnit::kS;
};

inline ParseResult31402 ParseTimescale31402(const std::string& src) {
  ParseResult31402 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  result.preproc_timescale = preproc.CurrentTimescale();
  result.has_preproc_timescale = preproc.HasTimescale();
  result.preproc_global_precision = preproc.GlobalPrecision();
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}
