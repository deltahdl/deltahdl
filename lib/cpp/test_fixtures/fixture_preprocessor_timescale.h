#pragma once

#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_parser.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// What a run of the preprocessor left behind for a case to make its claim
// about: the record of the run and the timescale state the preprocessor ended
// in. A `timescale it rejected still leaves that state behind, the default or
// whatever an earlier directive set, so the record holds the case to reading
// has_errors or diags as a ParseResult does.
struct PreprocTimescaleResult : RecordedRun {
  TimeScale timescale;
  TimeUnit global_precision;
  bool has_timescale;
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
  RecordDiagnostics(diag, result);
  return result;
}

// Alias for tests that use "Preprocess" as a 1-arg call.
inline PreprocTimescaleResult Preprocess(const std::string& src) {
  return PreprocessTimescale(src);
}

// What a run of the preprocessor and then the parser left behind for a case to
// make its claim about: everything a ParseResult holds, and the global
// precision the preprocessor ended with. It is a ParseResult, so a case handed
// one for a source that drew an error is held to reading has_errors or diags
// as a case handed ParseResult itself is: a rejected source still leaves a
// CompilationUnit of what the parser recovered and a global precision of
// whatever the preprocessor ended with, and an absence or a default asserted on
// either holds whether the rule it covers works or not.
struct PreprocessedParseResult : ParseResult {
  bool has_preproc_global_precision = false;
  TimeUnit preproc_global_precision = TimeUnit::kS;
};

inline PreprocessedParseResult PreprocessAndParse(const std::string& src) {
  PreprocessedParseResult result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  result.has_preproc_global_precision = preproc.HasGlobalPrecision();
  result.preproc_global_precision = preproc.GlobalPrecision();
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  RecordDiagnostics(diag, result);
  return result;
}
