#pragma once

#include <string>
#include <vector>

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
  // A copy rather than a view, because the engine that recorded them is a
  // local of the call below and its storage is gone once that call returns.
  std::vector<Diagnostic> diags;
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
  result.diags = diag.Diagnostics();
  return result;
}

// Alias for tests that use "Preprocess" as a 1-arg call.
inline PreprocTimescaleResult Preprocess(const std::string& src) {
  return PreprocessTimescale(src);
}

// What a run of the preprocessor and then the parser left behind for a case to
// make its claim about. The diagnostics are a copy rather than a view: the
// engine that recorded them is a local of the call that ran the parser, so a
// case reading the engine's own record would be reading storage released before
// the call returned.
//
// has_errors stays beside them, because a case asking only whether a source was
// accepted is asking a question the whole record does not answer more clearly
// than the boolean does.
struct ParseResult31402 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
  std::vector<Diagnostic> diags;
  TimeScale preproc_timescale;
  bool has_preproc_timescale = false;
  TimeUnit preproc_global_precision = TimeUnit::kS;
};

// Takes both readings of the engine at once, so no run can copy the record and
// leave the boolean behind, or the reverse.
inline void RecordDiagnostics(const DiagEngine& diag,
                              ParseResult31402& result) {
  result.has_errors = diag.HasErrors();
  result.diags = diag.Diagnostics();
}

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
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  RecordDiagnostics(diag, result);
  return result;
}
