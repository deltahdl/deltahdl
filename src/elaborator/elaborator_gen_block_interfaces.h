#pragma once

#include <functional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_module.h"

namespace delta {

using InterfaceInstTypes =
    std::unordered_map<std::string_view, std::string_view>;

std::string_view FindBlockInterface(std::string_view name,
                                    const GenBlockPrefixes& prefixes,
                                    const InterfaceInstTypes& table);

struct GenBlockContext {
  const HierPath& path;
  const GenBlockConsts& consts;
  const GenBlockPrefixes& prefixes;
};

void EnterGenBlockInstance(RtlirModuleInst& inst, const ModuleDecl* child_decl,
                           const GenBlockContext& context,
                           InterfaceInstTypes& table);

void RegisterGenerateBlockInterfaces(
    const std::vector<ModuleItem*>& items,
    const std::function<const ModuleDecl*(std::string_view)>& find_module,
    InterfaceInstTypes& table, Arena& arena);

struct InterfaceActualScope {
  const ModuleDecl* parent;
  const std::vector<const ModuleDecl*>& tops;
  const std::function<const ModuleDecl*(std::string_view)>& find_module;
  InterfaceInstTypes& table;
  const ScopeMap& params;
  Arena& arena;
  DiagEngine& diag;
  SourceLoc loc;
};

void ResolveGenBlockInterfaceActuals(RtlirModuleInst& inst,
                                     const InterfaceActualScope& scope);

void ResolveInstancePathActuals(RtlirModuleInst& inst,
                                const InterfaceActualScope& scope);

}  // namespace delta
