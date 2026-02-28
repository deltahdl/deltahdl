#pragma once

#include "fixture_parser.h"

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "preprocessor/preprocessor.h"

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

inline RtlirDesign* ElaborateSrc(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

inline RtlirDesign* Elaborate(const std::string& src, ElabFixture& f) {
  return ElaborateSrc(src, f);
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
