#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {
namespace {

// §26.4: the scopes an import registers a package item into. The typedef table
// and the set naming which of its entries stand for an unpacked aggregate are
// filled by the same declaration and travel together, the parameter scope is
// another part of what one import writes, and the class-name sets are the
// last: a package class the import makes visible is a class type in the
// importing scope (§26.3), which is what makes `B h;` declare a handle and
// lets `h = d` take a subclass handle (§8.13).
struct ImportScope {
  TypedefMap& typedefs;
  std::unordered_set<std::string_view>& aggregate_typedefs;
  ScopeMap& cu_param_scope;
  std::unordered_set<std::string_view>& class_names;
  std::unordered_set<std::string_view>& parameterized_classes;
  // §13.4.3: the functions the constant-expression folder may call, which an
  // imported package function joins under its bare name.
  std::unordered_map<std::string_view, const ModuleItem*>& func_decls;
};

// Register a single imported package item into a module's elaboration scopes:
// typedefs become available by name, const parameters are entered into the
// compilation-unit parameter scope, and classes into the class-name sets as
// RecordClassDecl enters a module's own (§8.25 for the parameterized ones).
// Shared by the wildcard and named-import branches of ApplyImport.
void RegisterImportItem(const ModuleItem* pi, std::string_view pkg_name,
                        std::string_view name, ImportScope scope) {
  if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl) {
    scope.class_names.insert(name);
    if (!pi->class_decl->params.empty()) {
      scope.parameterized_classes.insert(name);
    }
  } else if (pi->kind == ModuleItemKind::kFunctionDecl &&
             pi->method_class.empty()) {
    scope.func_decls[name] = pi;
  } else if (pi->kind == ModuleItemKind::kTypedef) {
    scope.typedefs[name] = pi->typedef_type;
    // §6.18: an import is what gives a package's typedef its bare name in this
    // scope, and the name stands for whatever the package declared -- an
    // aggregate when the declaration carried unpacked dimensions.
    if (!pi->unpacked_dims.empty()) scope.aggregate_typedefs.insert(name);
  } else if (pi->kind == ModuleItemKind::kParamDecl && pi->init_expr) {
    // RegisterPackageParams in elaborator_resolve.cpp folded the value where
    // the declaration stands, against the package's own earlier parameters
    // and the members of its enumerations (§6.19, §6.20.1), and recorded it
    // under the "package.name" key. This scope holds none of those bare
    // names, so the recorded value is read back rather than folded again; an
    // initializer registration could not fold is folded here as before.
    std::string qualified = std::string(pkg_name) + "." + std::string(pi->name);
    auto it = scope.cu_param_scope.find(qualified);
    if (it != scope.cu_param_scope.end()) {
      scope.cu_param_scope[name] = it->second;
      return;
    }
    auto val = FoldDeclaredParamValue(pi->init_expr, pi->data_type,
                                      scope.cu_param_scope);
    if (val) scope.cu_param_scope[name] = *val;
  }
}

// Locate a package declaration by name within the compilation unit, or nullptr.
const PackageDecl* FindPackageByName(const CompilationUnit* unit,
                                     std::string_view pkg_name) {
  for (const auto* p : unit->packages) {
    if (p->name == pkg_name) return p;
  }
  return nullptr;
}

// Register every named item of a wildcard-imported package.
void RegisterWildcardImport(const PackageDecl* pkg, ImportScope scope) {
  for (const auto* pi : pkg->items) {
    if (!pi->name.empty()) RegisterImportItem(pi, pkg->name, pi->name, scope);
  }
}

// Register a single named item of an explicitly-named package import.
void RegisterNamedImport(const PackageDecl* pkg, std::string_view target,
                         ImportScope scope) {
  for (const auto* pi : pkg->items) {
    if (pi->name == target) {
      RegisterImportItem(pi, pkg->name, target, scope);
      break;
    }
  }
}

// Apply one package import directive, resolving the named package and
// registering either all of its items (wildcard) or a single named item.
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

// §3.12.1 makes the compilation-unit scope the one a module's upward search
// (§23.9) ends in, and §26.3 has an import make a package's names visible in
// the scope it is written in; so an import written outside every module, as the
// uvm-tagged sv-tests files write `import uvm_pkg::*;` above their module, is
// in force in each module of the unit. Each module takes the unit's imports as
// it takes its own header imports, ahead of them so that a module's own
// declarations and imports shadow the unit's (§23.9), and each is recorded on
// the RTLIR module as a header import is, which is what the lowering reads.
void Elaborator::ApplyCompilationUnitImports(RtlirModule* mod) {
  for (const auto* item : unit_->cu_items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& imp = item->import_item;
    ApplyImport(imp, unit_,
                {typedefs_, aggregate_typedef_names_, cu_param_scope_,
                 class_names_, parameterized_class_names_, func_decls_});
    mod->imports.push_back(RtlirImport{imp.package_name, imp.item_name,
                                       imp.is_wildcard, std::string_view()});
  }
}

// §26.4: an import written in the module header precedes every declaration in
// the module, ports included, so these are applied before ports and before the
// item walk. A body import is applied by ApplyBodyImport below instead, as the
// walk reaches it.
void Elaborator::ApplyHeaderImports(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (!item->import_item.is_header) continue;
    ApplyImport(item->import_item, unit_,
                {typedefs_, aggregate_typedef_names_, cu_param_scope_,
                 class_names_, parameterized_class_names_, func_decls_});
  }
}

// §26.3: an identifier is potentially locally visible "at some point within a
// scope if there is a wildcard import of a package before that point within the
// current scope", and an explicit import makes one locally visible "prior to
// that point within the current scope". Both rules are about the import's
// position in the scope, which is why this registers one import as the item
// walk in Elaborator::ElaborateItems reaches it rather than hoisting every body
// import ahead of the walk: a declaration written above the import does not see
// the package, and one written below it does.
//
// A header import is already registered by ApplyHeaderImports before the walk
// starts and is skipped here.
void Elaborator::ApplyBodyImport(const ImportItem& import_item) {
  if (import_item.is_header) return;
  ApplyImport(import_item, unit_,
              {typedefs_, aggregate_typedef_names_, cu_param_scope_,
               class_names_, parameterized_class_names_, func_decls_});
}

}  // namespace delta
