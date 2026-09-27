#pragma once

#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/parser.h"

// One elaboration of a design under its configuration, held together so the
// design can be read after the run that built it.
struct ConfigElaboration {
  delta::SourceManager mgr;
  delta::Arena arena;
  delta::DiagEngine diag{mgr};
  delta::RtlirDesign* design = nullptr;
};

// Elaborates `src` under the first configuration it declares. Every module
// and configuration of `src` is put in the library work, as a command line with
// no library map compiles it (§33.3.1), so a rule naming work reaches them and
// a rule naming any other library reaches nothing.
inline void ElaborateUnderConfig(std::string_view src, ConfigElaboration& run) {
  auto fid = run.mgr.AddFile("<test>", std::string(src));
  delta::Lexer lex(run.mgr.FileContent(fid), fid, run.diag);
  delta::Parser parser(lex, run.arena, run.diag);
  auto* cu = parser.Parse();
  if (cu == nullptr || cu->configs.empty()) return;
  for (auto* mod : cu->modules) mod->library = "work";
  for (auto* cfg : cu->configs) cfg->library = "work";
  delta::Elaborator elab(run.arena, run.diag, cu);
  run.design = elab.Elaborate(cu->configs[0]);
}

// What elaborating `src` under its one configuration reports.
inline std::vector<delta::Diagnostic> ConfigElaborationReports(
    std::string_view src) {
  ConfigElaboration run;
  ElaborateUnderConfig(src, run);
  return run.diag.Diagnostics();
}
