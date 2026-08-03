#pragma once

#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// What a run of the parser left behind for a case to make its claim about. The
// diagnostics are a copy rather than a view: the engine that recorded them is
// a local of the call that ran the parser, so a case reading the engine's own
// record would be reading storage released before the call returned.
//
// has_errors stays beside them, because a case asking only whether a source
// was accepted is asking a question the whole record does not answer more
// clearly than the boolean does.
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
  std::vector<Diagnostic> diags;
};

// Takes both readings of the engine at once, so no run can copy the record and
// leave the boolean behind, or the reverse.
inline void RecordDiagnostics(const DiagEngine& diag, ParseResult& result) {
  result.has_errors = diag.HasErrors();
  result.diags = diag.Diagnostics();
}

inline ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  RecordDiagnostics(diag, result);
  return result;
}

// Answers whether the parser accepted `src`, for a case that asks nothing else
// about the run. Parse is what runs, so the answer here and the record a case
// reading Parse gets come from one parse of one source rather than from two
// that could drift apart.
inline bool ParseOk(const std::string& src) { return !Parse(src).has_errors; }

inline ParseResult ParseLibrary(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.ParseLibraryText();
  RecordDiagnostics(diag, result);
  return result;
}

inline ParseResult ParseWithPreprocessor(const std::string& src) {
  ParseResult result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.cu->default_nettype = preproc.DefaultNetType();
  result.cu->unconnected_drive = preproc.UnconnectedDrive();
  for (auto* mod : result.cu->modules) {
    for (const auto& cell_name : preproc.CellModuleNames()) {
      if (mod->name == cell_name) {
        mod->is_cell = true;
        break;
      }
    }
  }
  result.cu->default_decay_time = preproc.DefaultDecayTime();
  result.cu->default_decay_time_real = preproc.DefaultDecayTimeReal();
  result.cu->default_decay_time_infinite = preproc.DefaultDecayTimeInfinite();
  result.cu->default_trireg_strength = preproc.DefaultTriregStrength();
  result.cu->has_default_trireg_strength = preproc.HasDefaultTriregStrength();
  result.cu->delay_mode_directive = preproc.DelayModeDirective();
  RecordDiagnostics(diag, result);
  return result;
}

// The preprocessed counterpart of ParseOk, and written on the call above for
// the same reason.
inline bool ParseWithPreprocessorOk(const std::string& src) {
  return !ParseWithPreprocessor(src).has_errors;
}
