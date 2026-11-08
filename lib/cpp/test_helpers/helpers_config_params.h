#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "lexer/lexer.h"
#include "parser/ast_expr.h"
#include "parser/parser.h"

inline RtlirDesign* ConfigElab(ElabFixture& f, const std::string& src) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  f.has_errors.Record(src);
  return design;
}

inline RtlirModule* ConfigElabFirstChild(ElabFixture& f,
                                         const std::string& src) {
  auto* design = ConfigElab(f, src);
  if (!design || design->top_modules.empty()) return nullptr;
  auto* top = design->top_modules[0];
  if (top->children.empty()) return nullptr;
  return top->children[0].resolved;
}

inline int64_t ResolvedParam(const RtlirModule* m, std::string_view name) {
  for (const auto& p : m->params) {
    if (p.name == name) return p.resolved_value;
  }
  return -1;
}

inline const Expr* OverrideExpr(const RtlirModule* m, std::string_view name) {
  for (const auto& p : m->params) {
    if (p.name == name) return p.override_expr;
  }
  return nullptr;
}

inline uint32_t VariableWidth(const RtlirModule* m, std::string_view name) {
  for (const auto& v : m->variables) {
    if (v.name == name) return v.width;
  }
  return 0;
}
