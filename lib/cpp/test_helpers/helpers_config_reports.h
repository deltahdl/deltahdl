#pragma once

#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_diagnosed.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/parser.h"

inline void PlaceConfigsWithTheirTops(delta::CompilationUnit* cu) {
  for (auto* cfg : cu->configs) {
    if (cfg->design_cells.empty()) continue;
    for (const auto* mod : cu->modules) {
      if (mod->name == cfg->design_cells.front().cell) {
        cfg->library = mod->library;
      }
    }
  }
}

struct ConfigElaboration {
  delta::SourceManager mgr;
  delta::Arena arena;
  delta::DiagEngine diag{mgr};
  Diagnosed diagnosed{diag};
  delta::RtlirDesign* design = nullptr;
};

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

inline std::vector<delta::Diagnostic> ConfigElaborationReports(
    std::string_view src) {
  ConfigElaboration run;
  ElaborateUnderConfig(src, run);
  return run.diag.Diagnostics();
}
