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
  // With no explicit top and no top-level module (empty/whitespace/comment-only
  // or package/class-only source), pass an empty name; the elaborator validates
  // and elaborates the compilation unit as-is rather than dereferencing an
  // empty module list (which was undefined behavior, crashing on arm64).
  std::string_view name = top;
  if (name.empty() && !cu->modules.empty()) name = cu->modules.back()->name;
  auto* design = elab.Elaborate(name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

inline RtlirDesign* Elaborate(const std::string& src, ElabFixture& f,
                              std::string_view top = "") {
  return ElaborateSrc(src, f, top);
}

// Runs the preprocess -> parse prologue on an already-registered source file
// and returns the resulting CompilationUnit. The caller owns `preproc` so that
// it can read back preprocessor state after parsing.
inline CompilationUnit* PreprocessAndParseCu(ElabFixture& f, uint32_t fid,
                                             Preprocessor& preproc) {
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = f.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(f.mgr.FileContent(pp_fid), pp_fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  return parser.Parse();
}

// Propagates the decay-time, trireg-strength, and delay-mode directives from
// the preprocessor onto the CompilationUnit.
inline void PropagateDecayAndDelayToCu(CompilationUnit* cu,
                                       Preprocessor& preproc) {
  cu->default_decay_time = preproc.DefaultDecayTime();
  cu->default_decay_time_real = preproc.DefaultDecayTimeReal();
  cu->default_decay_time_infinite = preproc.DefaultDecayTimeInfinite();
  cu->default_trireg_strength = preproc.DefaultTriregStrength();
  cu->has_default_trireg_strength = preproc.HasDefaultTriregStrength();
  cu->delay_mode_directive = preproc.DelayModeDirective();
}

// When `auto_top` is set, no top module is named and the elaborator roots every
// uninstantiated module as a top (§23.3.1) rather than the single last module;
// used by tests that check multi-top designs.
inline RtlirDesign* ElaborateWithPreprocessor(const std::string& src,
                                              ElabFixture& f,
                                              std::string_view top = "",
                                              bool auto_top = false) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor preproc(f.mgr, f.diag, {});
  auto* cu = PreprocessAndParseCu(f, fid, preproc);
  // Propagate preprocessor state to CompilationUnit.
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
  PropagateDecayAndDelayToCu(cu, preproc);
  Elaborator elab(f.arena, f.diag, cu);
  // See ElaborateSrc: with no explicit top and no top-level module, pass an
  // empty name instead of dereferencing an empty module list.
  std::string_view name = top;
  if (!auto_top && name.empty() && !cu->modules.empty())
    name = cu->modules.back()->name;
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
