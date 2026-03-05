#pragma once

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"
#include "preprocessor/preprocessor.h"

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

inline RtlirDesign* ElaborateSrc(const std::string& src, ElabFixture& f,
                                 std::string_view top = "") {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto name = top.empty() ? cu->modules.back()->name : top;
  auto* design = elab.Elaborate(name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

inline RtlirDesign* Elaborate(const std::string& src, ElabFixture& f,
                              std::string_view top = "") {
  return ElaborateSrc(src, f, top);
}

inline RtlirDesign* ElaborateWithPreprocessor(const std::string& src,
                                               ElabFixture& f,
                                               std::string_view top = "") {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor preproc(f.mgr, f.diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = f.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(f.mgr.FileContent(pp_fid), pp_fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  // Propagate preprocessor state to CompilationUnit.
  cu->default_nettype = preproc.DefaultNetType();
  cu->default_decay_time = preproc.DefaultDecayTime();
  cu->default_decay_time_real = preproc.DefaultDecayTimeReal();
  cu->default_decay_time_infinite = preproc.DefaultDecayTimeInfinite();
  cu->default_trireg_strength = preproc.DefaultTriregStrength();
  cu->has_default_trireg_strength = preproc.HasDefaultTriregStrength();
  cu->delay_mode_directive = preproc.DelayModeDirective();
  Elaborator elab(f.arena, f.diag, cu);
  auto name = top.empty() ? cu->modules.back()->name : top;
  auto* design = elab.Elaborate(name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

inline bool ElabOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, arena, diag);
  auto* cu = parser.Parse();
  if (diag.HasErrors() || cu->modules.empty()) return false;
  Elaborator elab(arena, diag, cu);
  elab.Elaborate(cu->modules.back()->name);
  return !diag.HasErrors();
}
