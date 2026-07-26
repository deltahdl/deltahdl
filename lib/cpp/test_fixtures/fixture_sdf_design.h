#pragma once

#include <string>

#include "elaborator/elaborator.h"
#include "fixture_simulator.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"

using namespace delta;

// A SystemVerilog design carried far enough that a SpecifyManager can be bound
// to it, for a test whose subject is SDF annotation. Nothing on the design
// side is hand-assembled: the module is parsed, elaborated and lowered from
// real source, and what the manager learns about it comes from the production
// collectors. What a design's specify data means differs by subclause, so this
// carries the design and leaves the binding to the caller.
struct SdfDesign {
  SimFixture f;
  SpecifyManager mgr;
  CompilationUnit* cu = nullptr;
  RtlirDesign* design = nullptr;

  // Parses, elaborates and lowers `src`, returning false when any of the three
  // fails. The design is lowered but not run, so a caller that wants to
  // observe a procedural delay reading an annotated value can annotate first
  // and run afterwards.
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

  // The top module: the last one the source declares.
  const ModuleDecl& Top() const { return *cu->modules.back(); }

  // Registers `mod`'s module path declarations and timing checks with the
  // manager through the production builders, which is what makes them
  // annotatable.
  void AddPathsAndTimingChecks(const ModuleDecl& mod) {
    for (auto* item : mod.items) {
      if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
      for (auto* si : item->specify_items) {
        if (si->kind == SpecifyItemKind::kPathDecl) {
          mgr.AddPathDelayFromDecl(si->path, f.ctx, f.arena);
        } else if (si->kind == SpecifyItemKind::kTimingCheck) {
          mgr.AddTimingCheckUnderOptions(si->timing_check, f.ctx, f.arena);
        }
      }
    }
  }
};
