#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_diagnosed.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  Diagnosed has_errors{diag};

  std::function<void(Elaborator&)> configure;
};

inline RtlirDesign* ElaborateSrcReportingParse(const std::string& src,
                                               ElabFixture& f,
                                               std::string_view top,
                                               bool& parse_failed) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  uint32_t errors_before_parse = f.diag.ErrorCount();
  auto* cu = parser.Parse();
  parse_failed = f.diag.ErrorCount() != errors_before_parse;
  Elaborator elab(f.arena, f.diag, cu);
  if (f.configure) f.configure(elab);
  std::string_view name = top;
  if (name.empty() && !cu->modules.empty()) name = cu->modules.back()->name;
  auto* design = elab.Elaborate(name);
  f.has_errors.Record(src);
  return design;
}

inline RtlirDesign* ElaborateSrc(const std::string& src, ElabFixture& f,
                                 std::string_view top = "") {
  bool parse_failed = false;
  auto* design = ElaborateSrcReportingParse(src, f, top, parse_failed);
  if (parse_failed) {
    f.has_errors.Excuse();
    ADD_FAILURE() << "the source did not parse, so nothing but a fragment was "
                     "elaborated and every answer about elaboration is "
                     "vacuous:\n"
                  << src;
  }
  return design;
}

inline RtlirDesign* ElaborateSrcAllowingParseErrors(const std::string& src,
                                                    ElabFixture& f,
                                                    std::string_view top = "") {
  bool parse_failed = false;
  return ElaborateSrcReportingParse(src, f, top, parse_failed);
}

inline RtlirDesign* Elaborate(const std::string& src, ElabFixture& f,
                              std::string_view top = "") {
  return ElaborateSrc(src, f, top);
}

inline CompilationUnit* PreprocessAndParseCu(ElabFixture& f, uint32_t fid,
                                             Preprocessor& preproc) {
  auto pp = preproc.Preprocess(fid);
  auto pp_fid =
      f.mgr.AddPreprocessedFile("<preprocessed>", pp, preproc.LineOrigins());
  Lexer lexer(f.mgr.FileContent(pp_fid), pp_fid, f.diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, f.arena, f.diag);
  return parser.Parse();
}

inline void PropagateDirectivesToCu(CompilationUnit* cu,
                                    Preprocessor& preproc) {
  cu->default_decay_time = preproc.DefaultDecayTime();
  cu->default_decay_time_real = preproc.DefaultDecayTimeReal();
  cu->default_decay_time_infinite = preproc.DefaultDecayTimeInfinite();
  cu->default_trireg_strength = preproc.DefaultTriregStrength();
  cu->has_default_trireg_strength = preproc.HasDefaultTriregStrength();
  ApplyModuleDirectives(cu, preproc.ModuleDirectivesList());
  cu->delay_mode_directive = preproc.DelayModeDirective();
  cu->has_preproc_global_precision = preproc.HasGlobalPrecision();
  cu->preproc_global_precision = preproc.GlobalPrecision();
  cu->preproc_global_precision_magnitude = preproc.GlobalPrecisionMagnitude();
}

inline RtlirDesign* ElaborateWithPreprocessorReportingParse(
    const std::string& src, ElabFixture& f, std::string_view top, bool auto_top,
    bool& parse_failed) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor preproc(f.mgr, f.diag, {});
  uint32_t errors_before_parse = f.diag.ErrorCount();
  auto* cu = PreprocessAndParseCu(f, fid, preproc);
  parse_failed = f.diag.ErrorCount() != errors_before_parse;
  cu->default_nettype = preproc.DefaultNetType();
  cu->unconnected_drive = preproc.UnconnectedDrive();
  for (auto* mod : cu->modules) {
    for (const auto& cell_name : preproc.CellModuleNames()) {
      if (mod->name == cell_name) {
        mod->is_cell = true;
        break;
      }
    }
  }
  PropagateDirectivesToCu(cu, preproc);
  Elaborator elab(f.arena, f.diag, cu);
  if (f.configure) f.configure(elab);
  std::string_view name = top;
  if (!auto_top && name.empty() && !cu->modules.empty())
    name = cu->modules.back()->name;
  auto* design = elab.Elaborate(name);
  f.has_errors.Record(src);
  return design;
}

inline RtlirDesign* ElaborateWithPreprocessor(const std::string& src,
                                              ElabFixture& f,
                                              std::string_view top = "",
                                              bool auto_top = false) {
  bool parse_failed = false;
  auto* design = ElaborateWithPreprocessorReportingParse(src, f, top, auto_top,
                                                         parse_failed);
  if (parse_failed) {
    f.has_errors.Excuse();
    ADD_FAILURE()
        << "the source did not preprocess and parse, so nothing but a "
           "fragment was elaborated and every answer about "
           "elaboration is vacuous:\n"
        << src;
  }
  return design;
}

inline RtlirDesign* ElaborateWithPreprocessorAllowingParseErrors(
    const std::string& src, ElabFixture& f, std::string_view top = "",
    bool auto_top = false) {
  bool parse_failed = false;
  return ElaborateWithPreprocessorReportingParse(src, f, top, auto_top,
                                                 parse_failed);
}

inline bool ElabOk(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor preproc(f.mgr, f.diag, {});
  auto* cu = PreprocessAndParseCu(f, fid, preproc);
  f.has_errors.Record(src);
  if (f.has_errors) {
    ADD_FAILURE() << "the source did not parse, so nothing was elaborated "
                     "and every answer about elaboration is vacuous:\n"
                  << src;
    return false;
  }
  Elaborator elab(f.arena, f.diag, cu);
  if (f.configure) f.configure(elab);
  std::string_view top =
      cu->modules.empty() ? std::string_view{} : cu->modules.back()->name;
  elab.Elaborate(top);
  f.has_errors.Record(src);
  return !f.has_errors;
}

inline bool ElabOk(const std::string& src) {
  ElabFixture f;
  return ElabOk(src, f);
}

inline const Diagnostic* FindDiag(const ElabFixture& f,
                                  std::string_view needle) {
  for (const auto& diag : f.diag.Diagnostics()) {
    if (diag.message.find(needle) != std::string::npos) return &diag;
  }
  return nullptr;
}
