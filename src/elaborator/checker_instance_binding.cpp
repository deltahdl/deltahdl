#include "elaborator/checker_instance_binding.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

// §17.2: the checker `name` the package `pkg` declares, or nullptr.
ModuleDecl* PackageChecker(const CompilationUnit* unit, std::string_view pkg,
                           std::string_view name) {
  for (const PackageDecl* package : unit->packages) {
    if (package->name != pkg) continue;
    for (const ModuleItem* item : package->items) {
      const ModuleDecl* decl = item->nested_module_decl;
      if (item->kind == ModuleItemKind::kNestedModuleDecl && decl != nullptr &&
          decl->name == name && decl->decl_kind == ModuleDeclKind::kChecker) {
        return item->nested_module_decl;
      }
    }
  }
  return nullptr;
}

}  // namespace

ModuleDecl* PackageCheckerNamedBy(const ModuleItem* item,
                                  const RtlirModule* mod,
                                  const CompilationUnit* unit) {
  if (!item->inst_scope.empty()) {
    return PackageChecker(unit, item->inst_scope, item->inst_module);
  }
  for (const RtlirImport& imp : mod->imports) {
    if (!imp.is_wildcard && imp.item_name != item->inst_module) continue;
    if (ModuleDecl* found =
            PackageChecker(unit, imp.package_name, item->inst_module)) {
      return found;
    }
  }
  return nullptr;
}

BoundCheckerFormals BindCheckerActuals(const ModuleItem* item,
                                       const ModuleDecl* decl,
                                       const ScopeMap& scope) {
  BoundCheckerFormals bound;
  for (size_t i = 0; i < item->inst_ports.size(); ++i) {
    auto [name, actual] = item->inst_ports[i];
    if (name.empty() && i < decl->ports.size()) name = decl->ports[i].name;
    bound.emplace_back(name, ConstEvalInt(actual, scope));
  }
  return bound;
}

ActualsByFormal CheckerTreeActuals(const ModuleItem* item,
                                   const ModuleDecl* decl) {
  ActualsByFormal actuals;
  for (size_t i = 0; i < item->inst_ports.size(); ++i) {
    auto [name, actual] = item->inst_ports[i];
    if (name.empty() && i < decl->ports.size()) name = decl->ports[i].name;
    if (actual != nullptr && actual->property_actual != nullptr) {
      actuals[name] = actual;
    }
  }
  return actuals;
}

void ReportActualsOnlyACheckerTakes(const RtlirModuleInst& inst,
                                    const ModuleItem* item, DiagEngine& diag) {
  if (inst.resolved == nullptr || inst.resolved->is_checker) return;
  for (const auto& [name, actual] : item->inst_ports) {
    if (actual == nullptr ||
        (actual->property_actual == nullptr && !IsEventActual(actual))) {
      continue;
    }
    diag.Error(actual->range.start,
               "port connection of instance '" + std::string(item->inst_name) +
                   "' is an event expression, a sequence or a property, "
                   "which only a checker's port takes",
               Subclause("23.3.2"));
  }
}

ConstantCheckerFormals CheckerConstantFormals(const ModuleDecl* decl,
                                              const BoundCheckerFormals& bound,
                                              const ScopeMap& scope) {
  ConstantCheckerFormals formals;
  for (const PortDecl& port : decl->ports) {
    auto it = std::find_if(bound.begin(), bound.end(), [&](const auto& entry) {
      return entry.first == port.name;
    });
    std::optional<int64_t> value =
        it != bound.end() ? it->second
                          : ConstEvalInt(port.default_value, scope);
    if (value) formals.emplace_back(port.name, *value);
  }
  return formals;
}

std::vector<std::string_view> CheckerFreeVariables(const ModuleDecl* decl) {
  std::vector<std::string_view> free;
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->is_rand) {
      free.push_back(item->name);
    }
  }
  return free;
}

}  // namespace delta
