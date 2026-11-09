#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/nettype_registration.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "elaborator/unit_scope_order.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {
namespace {

struct ImportScope {
  TypedefMap& typedefs;
  std::unordered_set<std::string_view>& aggregate_typedefs;
  ScopeMap& cu_param_scope;
  std::unordered_set<std::string_view>& class_names;
  std::unordered_set<std::string_view>& parameterized_classes;
  std::unordered_map<std::string_view, const ModuleItem*>& func_decls;
  NettypeTables nettypes;
  Arena& arena;
};

void RegisterImportedNettype(std::string_view pkg, std::string_view nettype,
                             std::string_view name, const ImportScope& scope) {
  CopyNettype(std::string(pkg) + "::" + std::string(nettype), name,
              scope.typedefs, scope.nettypes);
}

void RegisterImportedParam(const ModuleItem* pi, const PackageDecl& pkg,
                           std::string_view name, const ImportScope& scope) {
  std::string qualified = std::string(pkg.name) + "." + std::string(pi->name);
  auto it = scope.cu_param_scope.find(qualified);
  if (it != scope.cu_param_scope.end()) {
    scope.cu_param_scope[name] = it->second;
    SetTwoStateReading(
        scope.cu_param_scope, name,
        RecordedTwoStateReading(scope.cu_param_scope, qualified));
    return;
  }
  const DataType kType = InPackageScope(pi->data_type, pkg);
  auto val = FoldDeclaredParamValue(pi->init_expr, kType, scope.cu_param_scope);
  if (!val) return;
  scope.cu_param_scope[name] = *val;
  SetTwoStateReading(
      scope.cu_param_scope, name,
      TwoStateReading(pi->init_expr, kType, scope.cu_param_scope, *val));
}

void RegisterImportItem(const ModuleItem* pi, const PackageDecl& pkg,
                        std::string_view name, ImportScope scope) {
  if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl) {
    scope.class_names.insert(name);
    if (!pi->class_decl->params.empty()) {
      scope.parameterized_classes.insert(name);
    }
  } else if (pi->kind == ModuleItemKind::kFunctionDecl &&
             pi->method_class.empty()) {
    scope.func_decls[name] = pi;
  } else if (pi->kind == ModuleItemKind::kNettypeDecl) {
    RegisterImportedNettype(pkg.name, pi->name, name, scope);
  } else if (pi->kind == ModuleItemKind::kTypedef) {
    scope.typedefs[name] = PackageTypedefType(*pi, pkg, scope.arena);
    if (!pi->unpacked_dims.empty()) scope.aggregate_typedefs.insert(name);
  } else if (pi->kind == ModuleItemKind::kParamDecl && pi->init_expr) {
    RegisterImportedParam(pi, pkg, name, scope);
  }
}

const PackageDecl* FindPackageByName(const CompilationUnit* unit,
                                     std::string_view pkg_name) {
  for (const auto* p : unit->packages) {
    if (p->name == pkg_name) return p;
  }
  return nullptr;
}

void RegisterWildcardImport(const PackageDecl* pkg, ImportScope scope) {
  for (const auto* pi : pkg->items) {
    if (!pi->name.empty()) RegisterImportItem(pi, *pkg, pi->name, scope);
  }
}

void RegisterNamedImport(const PackageDecl* pkg, std::string_view target,
                         ImportScope scope) {
  for (const auto* pi : pkg->items) {
    if (pi->name == target) {
      RegisterImportItem(pi, *pkg, target, scope);
      break;
    }
  }
}

void ApplyImport(const ImportItem& import_item, const CompilationUnit* unit,
                 ImportScope scope) {
  const PackageDecl* pkg = FindPackageByName(unit, import_item.package_name);
  if (!pkg) return;
  if (import_item.is_wildcard) {
    RegisterWildcardImport(pkg, scope);
  } else {
    RegisterNamedImport(pkg, import_item.item_name, scope);
  }
}

}  // namespace

void Elaborator::ApplyCompilationUnitImports(const ModuleDecl* decl,
                                             RtlirModule* mod) {
  for (const auto* item : UnitItemsBefore(unit_, decl->range.start)) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& imp = item->import_item;
    ApplyImport(imp, unit_,
                {typedefs_,
                 aggregate_typedef_names_,
                 cu_param_scope_,
                 class_names_,
                 parameterized_class_names_,
                 func_decls_,
                 {nettype_names_, nettype_resolve_funcs_, nettype_canonical_},
                 arena_});
    mod->imports.push_back(RtlirImport{imp.package_name, imp.item_name,
                                       imp.is_wildcard, std::string_view()});
  }
}

void Elaborator::ApplyHeaderImports(const ModuleDecl* decl, RtlirModule* mod) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& imp = item->import_item;
    if (!imp.is_header) continue;
    ApplyImport(imp, unit_,
                {typedefs_,
                 aggregate_typedef_names_,
                 cu_param_scope_,
                 class_names_,
                 parameterized_class_names_,
                 func_decls_,
                 {nettype_names_, nettype_resolve_funcs_, nettype_canonical_},
                 arena_});
    mod->imports.push_back(RtlirImport{imp.package_name, imp.item_name,
                                       imp.is_wildcard, std::string_view()});
  }
}

void Elaborator::ApplyBodyImport(const ImportItem& import_item) {
  if (import_item.is_header) return;
  ApplyImport(import_item, unit_,
              {typedefs_,
               aggregate_typedef_names_,
               cu_param_scope_,
               class_names_,
               parameterized_class_names_,
               func_decls_,
               {nettype_names_, nettype_resolve_funcs_, nettype_canonical_},
               arena_});
  inference_funcs_.funcs.insert(func_decls_.begin(), func_decls_.end());
}

}  // namespace delta
