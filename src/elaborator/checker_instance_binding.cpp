#include "elaborator/checker_instance_binding.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
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

// A.4.1 writes four instantiation forms, and three of them are one form under
// three identifier classes: `module_instantiation`, `interface_instantiation`
// and `program_instantiation` each read
// `<identifier> [ parameter_value_assignment ] hierarchical_instance
// { , hierarchical_instance } ;`. The fourth is deliberately narrower --
//
//     checker_instantiation ::=
//         ps_checker_identifier name_of_instance
//         ( [ list_of_checker_port_connections ] ) ;
//
// -- and what it leaves out is the parameter value assignment and the
// `{ , hierarchical_instance }` after the first instance. A checker takes its
// arguments through the ports that connection list fills (§17.3), so an
// override written before the instance name names nothing the declaration has;
// and one instantiation names one instance of it. Parsed by the one path all
// four forms share, an override was read as the parameter value assignment of
// the other three and carried to a declaration that has no parameters for it
// to override, and `chk c1(a), c2(b);` was read as the other three's list and
// elaborated as two instances, both silently.
void CheckCheckerInstForm(const ModuleItem* item, const ModuleDecl* child,
                          DiagEngine& diag) {
  if (child->decl_kind != ModuleDeclKind::kChecker) return;
  if (!item->inst_params.empty()) {
    diag.Error(item->loc,
               std::format("checker '{}' cannot be instantiated with a "
                           "parameter value assignment",
                           item->inst_module),
               Subclause("A.4.1.4"));
  }
  if (item->inst_continues_list) {
    diag.Error(item->loc,
               std::format("checker '{}' is instantiated one instance to an "
                           "instantiation; '{}' after a ',' is a second",
                           item->inst_module, item->inst_name),
               Subclause("A.4.1.4"));
  }
}

}  // namespace delta
