#pragma once

#include <string>
#include <string_view>

#include "fixture_elaborator.h"

using namespace delta;

// Bundles the elaboration fixture together with the CompilationUnit and the
// elaborated RtlirDesign so generate-construct tests can inspect both the
// parsed module items and the final design.
struct GenerateElab {
  ElabFixture f;
  CompilationUnit* cu = nullptr;
  RtlirDesign* design = nullptr;
};

// Parses and elaborates `src`, returning the fixture, CompilationUnit, and the
// resulting design. `top` selects the top module (defaults to the last module).
inline GenerateElab RunGenerateElaboration(const std::string& src,
                                           std::string_view top = "") {
  GenerateElab r;
  auto fid = r.f.mgr.AddFile("<test>", src);
  Lexer lexer(r.f.mgr.FileContent(fid), fid, r.f.diag);
  Parser parser(lexer, r.f.arena, r.f.diag);
  r.cu = parser.Parse();
  if (!r.cu) return r;
  auto name = top.empty() ? r.cu->modules.back()->name : top;
  Elaborator elab(r.f.arena, r.f.diag, r.cu);
  r.design = elab.Elaborate(name);
  r.f.has_errors = r.f.diag.HasErrors();
  return r;
}
