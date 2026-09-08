#include <optional>
#include <string_view>
#include <unordered_set>

#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "parser/ast.h"

namespace delta {
namespace {

// §26.4: the scopes an import registers a package item into. The typedef table
// and the set naming which of its entries stand for an unpacked aggregate are
// filled by the same declaration and travel together, and the parameter scope
// is the other half of what one import writes.
struct ImportScope {
  TypedefMap& typedefs;
  std::unordered_set<std::string_view>& aggregate_typedefs;
  ScopeMap& cu_param_scope;
};

// Register a single imported package item into a module's elaboration scopes:
// typedefs become available by name, and const parameters are folded into the
// compilation-unit parameter scope. Shared by the wildcard and named-import
// branches of ApplyImport.
void RegisterImportItem(const ModuleItem* pi, std::string_view name,
                        ImportScope scope) {
  if (pi->kind == ModuleItemKind::kTypedef) {
    scope.typedefs[name] = pi->typedef_type;
    // §6.18: an import is what gives a package's typedef its bare name in this
    // scope, and the name stands for whatever the package declared -- an
    // aggregate when the declaration carried unpacked dimensions.
    if (!pi->unpacked_dims.empty()) scope.aggregate_typedefs.insert(name);
  } else if (pi->kind == ModuleItemKind::kParamDecl && pi->init_expr) {
    auto val = ConstEvalInt(pi->init_expr, scope.cu_param_scope);
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
    if (!pi->name.empty()) RegisterImportItem(pi, pi->name, scope);
  }
}

// Register a single named item of an explicitly-named package import.
void RegisterNamedImport(const PackageDecl* pkg, std::string_view target,
                         ImportScope scope) {
  for (const auto* pi : pkg->items) {
    if (pi->name == target) {
      RegisterImportItem(pi, target, scope);
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

// §26.4: an import written in the module header precedes every declaration in
// the module, ports included, so these are applied before ports and before the
// item walk. A body import is applied by ApplyBodyImport below instead, as the
// walk reaches it.
void Elaborator::ApplyHeaderImports(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (!item->import_item.is_header) continue;
    ApplyImport(item->import_item, unit_,
                {typedefs_, aggregate_typedef_names_, cu_param_scope_});
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
              {typedefs_, aggregate_typedef_names_, cu_param_scope_});
}

}  // namespace delta
