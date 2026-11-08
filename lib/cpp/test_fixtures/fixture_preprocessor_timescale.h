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

inline PreprocTimescaleResult Preprocess(const std::string& src) {
  return PreprocessTimescale(src);
}

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
