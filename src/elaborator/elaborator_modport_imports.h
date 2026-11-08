#pragma once

#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "parser/ast_module.h"

namespace delta {

bool PrototypeMatchesSubroutine(const ModuleItem* proto,
                                const ModuleItem* body);

void CheckModportImport(const ModuleDecl* iface, const ModportDecl* mp,
                        const ModportPort& port, DiagEngine& diag);

struct SelectedModport {
  const ModuleDecl* iface;
  const ModportDecl* modport;
};
using SelectedModports = std::unordered_map<std::string_view, SelectedModport>;

void CheckModportImportCalls(const ModuleDecl* decl,
                             const SelectedModports& ports, DiagEngine& diag);

}  // namespace delta
