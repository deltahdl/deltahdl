#pragma once

#include "fixture_parser.h"

#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"

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
