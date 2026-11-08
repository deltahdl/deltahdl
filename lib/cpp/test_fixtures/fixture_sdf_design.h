#pragma once

#include <string>

#include "elaborator/elaborator.h"
#include "fixture_simulator.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/parser.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"

using namespace delta;

struct SdfDesign {
  SimFixture f;
  SpecifyManager mgr;
  CompilationUnit* cu = nullptr;
  RtlirDesign* design = nullptr;

  bool Lower(const std::string& src) {
    auto fid = f.mgr.AddFile("<test>", src);
    Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
    Parser parser(lexer, f.arena, f.diag);
    cu = parser.Parse();
    if (cu == nullptr || cu->modules.empty()) return false;
    Elaborator elab(f.arena, f.diag, cu);
    design = elab.Elaborate(cu->modules.back()->name);
    if (design == nullptr) return false;

    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    return true;
  }

  const ModuleDecl& Top() const { return *cu->modules.back(); }

  void AddPathDelays(const ModuleDecl& mod) {
    for (auto* item : mod.items) {
      if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
      for (auto* si : item->specify_items) {
        if (si->kind == SpecifyItemKind::kPathDecl) {
          mgr.AddPathDelayFromDecl(si->path, f.ctx, f.arena);
        }
      }
    }
  }

  void AddPathsAndTimingChecks(const ModuleDecl& mod) {
    AddPathDelays(mod);
    for (auto* item : mod.items) {
      if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
      for (auto* si : item->specify_items) {
        if (si->kind == SpecifyItemKind::kTimingCheck) {
          mgr.AddTimingCheckUnderOptions(si->timing_check, f.ctx, f.arena);
        }
      }
    }
  }
};
