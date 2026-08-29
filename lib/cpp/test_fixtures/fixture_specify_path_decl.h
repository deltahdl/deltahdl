#pragma once

#include <string>

#include "elaborator/elaborator.h"
#include "fixture_simulator.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

// Builders that produce a module path declaration from real specify-block
// source, for a test whose subject is a rule about a path delay. Writing the
// declaration out as source is what makes the SpecifyPathDecl genuine: the
// length of the right-hand side list drives delay_count, and each delay is a
// real path_delay_expression rather than a hand-filled array.

// The first module path declaration in a module carrying `specify_body`, or
// nullptr when the body declares none. The fixture is caller-owned, so the
// arena that holds the declaration outlives the call.
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

// A parsed path declaration together with the design it was elaborated from,
// so a delay expression that reads a specparam can be observed end to end: the
// specparam's value becomes resolvable only once the design is elaborated.
struct ElaboratedPathDecl {
  const SpecifyPathDecl* decl = nullptr;
  RtlirDesign* design = nullptr;
};

// Parses and elaborates a module carrying `port_header` ports plus
// `specify_body`, returning the first path declaration with that design.
// Lowering the design seeds each specify-block specparam as a context
// variable, so EvalExpr resolves those identifiers when a path delay is built
// from the declaration.
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
