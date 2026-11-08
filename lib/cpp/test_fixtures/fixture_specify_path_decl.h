#pragma once

#include <string>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "lexer/lexer.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/parser.h"

using namespace delta;

inline const SpecifyPathDecl* FirstPathDecl(const std::string& specify_body,
                                            SimFixture& f) {
  std::string code =
      "module t;\n  specify\n" + specify_body + "\n  endspecify\nendmodule\n";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  for (auto* mod : cu->modules) {
    for (auto* item : mod->items) {
      if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
      for (auto* si : item->specify_items) {
        if (si->kind == SpecifyItemKind::kPathDecl) return &si->path;
      }
    }
  }
  return nullptr;
}

struct ElaboratedPathDecl {
  const SpecifyPathDecl* decl = nullptr;
  RtlirDesign* design = nullptr;
};

inline ElaboratedPathDecl ElaboratePathDecl(const std::string& port_header,
                                            const std::string& specify_body,
                                            SimFixture& f) {
  std::string code = "module t(" + port_header + ");\n  specify\n" +
                     specify_body + "\n  endspecify\nendmodule\n";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  ElaboratedPathDecl out;
  out.design = elab.Elaborate(cu->modules.back()->name);
  for (auto* mod : cu->modules) {
    for (auto* item : mod->items) {
      if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
      for (auto* si : item->specify_items) {
        if (si->kind != SpecifyItemKind::kPathDecl) continue;
        out.decl = &si->path;
        return out;
      }
    }
  }
  return out;
}
