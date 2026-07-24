#include <algorithm>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec.h"

namespace delta {

PackageDecl* Lowerer::FindPackage(std::string_view name) const {
  if (!design_) return nullptr;
  for (auto* pkg : design_->packages) {
    if (pkg->name == name) return pkg;
  }
  return nullptr;
}

void Lowerer::LowerPackageItem(ModuleItem* item) {
  if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
    if (!ctx_.FindClassType(item->class_decl->name)) {
      LowerClassDecl(item->class_decl);
    }
  } else if (item->kind == ModuleItemKind::kFunctionDecl ||
             item->kind == ModuleItemKind::kTaskDecl) {
    if (!ctx_.FindFunction(item->name)) {
      ctx_.RegisterFunction(item->name, item);
    }
  }
}

static bool PackageItemHasName(const ModuleItem* item, std::string_view name) {
  if (item->name == name) return true;
  if (item->kind == ModuleItemKind::kClassDecl && item->class_decl &&
      item->class_decl->name == name)
    return true;
  return false;
}

static bool IsImportOrExportDecl(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kImportDecl ||
         item->kind == ModuleItemKind::kExportDecl;
}

static ModuleItem* FindNamedPackageItem(PackageDecl* pkg,
                                        std::string_view name) {
  for (auto* item : pkg->items) {
    if (IsImportOrExportDecl(item)) continue;
    if (PackageItemHasName(item, name)) return item;
  }
  return nullptr;
}

// Collects the package names imported by `pkg`, which a wildcard ("*")
// export re-exports from. The caller resolves each name and recurses.
static std::vector<std::string_view> WildcardExportImportNames(
    const PackageDecl* pkg) {
  std::vector<std::string_view> names;
  for (auto* imp_item : pkg->items) {
    if (imp_item->kind != ModuleItemKind::kImportDecl) continue;
    names.push_back(imp_item->import_item.package_name);
  }
  return names;
}

// Defined below; forward-declared so the name-resolution helpers can alias a
// re-exported package data item from the package that actually declares it.
static void AliasPackageDataItem(const PackageDecl* pkg, const ModuleItem* item,
                                 SimContext& ctx);

void Lowerer::LowerImportedName(
    PackageDecl* pkg, std::string_view name,
    std::unordered_set<const PackageDecl*>& visited) {
  if (!visited.insert(pkg).second) return;
  if (auto* found = FindNamedPackageItem(pkg, name)) {
    LowerPackageItem(found);
    // §26.6: an `export pkg::name` makes the given declaration available to a
    // downstream import following the same rules as a direct import. When that
    // declaration is a parameter or variable, its downstream visibility comes
    // from aliasing the unqualified name to the qualified name in the package
    // that declares it. LowerPackageItem only handles subroutines/classes, so
    // alias the data item here from `pkg` -- the origin package where `found`
    // is declared -- so a re-exported constant/variable resolves at runtime.
    AliasPackageDataItem(pkg, found, ctx_);
    return;
  }

  auto recurse = [&](std::string_view pkg_name) {
    auto* src = FindPackage(pkg_name);
    if (!src) return;
    auto sub = visited;
    LowerImportedName(src, name, sub);
  };
  auto handle_export = [&](const ImportItem& ex) {
    if (ex.package_name == "*") {
      for (std::string_view src_name : WildcardExportImportNames(pkg))
        recurse(src_name);
    } else if (ex.is_wildcard || ex.item_name == name) {
      recurse(ex.package_name);
    }
  };

  for (auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kExportDecl) continue;
    handle_export(item->import_item);
  }
}

// State shared by the free helpers that walk one package's export declarations
// for a wildcard import (§26.5). `lower_all`/`lower_named` forward back into
// the owning Lowerer so the recursion lives outside LowerAllImported's own
// body, keeping its cognitive complexity low. Each callback already snapshots
// the visited set, so it is passed by const reference here.
namespace {
struct ReExportWalk {
  PackageDecl* pkg;
  const std::unordered_set<const PackageDecl*>& visited;
  std::function<PackageDecl*(std::string_view)> find_pkg;
  std::function<void(PackageDecl*)> lower_all;
  std::function<void(PackageDecl*, std::string_view)> lower_named;
};

void ReExportAll(const ReExportWalk& w, PackageDecl* src) { w.lower_all(src); }

// Handles `export *::*;`: re-exports everything from each package `pkg`
// imports.
void ReExportWildcardStar(const ReExportWalk& w) {
  for (std::string_view src_name : WildcardExportImportNames(w.pkg)) {
    if (auto* src = w.find_pkg(src_name)) ReExportAll(w, src);
  }
}

// Handles one resolved `export pkg::item;` / `export pkg::*;`.
void ReExportFromPackage(const ReExportWalk& w, PackageDecl* src,
                         const ImportItem& ex) {
  if (ex.is_wildcard) {
    ReExportAll(w, src);
  } else {
    w.lower_named(src, ex.item_name);
  }
}

// Dispatches one export declaration to the matching re-export handler.
void HandleReExport(const ReExportWalk& w, const ImportItem& ex) {
  if (ex.package_name == "*") {
    ReExportWildcardStar(w);
  } else if (auto* src = w.find_pkg(ex.package_name)) {
    ReExportFromPackage(w, src, ex);
  }
}
}  // namespace

void Lowerer::LowerAllImported(
    PackageDecl* pkg, std::unordered_set<const PackageDecl*>& visited) {
  if (!visited.insert(pkg).second) return;
  for (auto* item : pkg->items) {
    if (IsImportOrExportDecl(item)) continue;
    LowerPackageItem(item);
    // §26.6: mirror the named-import path -- a data declaration reached by
    // lowering all of a (possibly re-exported) package must also be aliased
    // from this package so a wildcard consumer of a re-exported constant or
    // variable can resolve it at runtime.
    AliasPackageDataItem(pkg, item, ctx_);
  }

  ReExportWalk walk{pkg, visited,
                    [this](std::string_view name) { return FindPackage(name); },
                    [this, &visited](PackageDecl* src) {
                      auto sub = visited;
                      LowerAllImported(src, sub);
                    },
                    [this, &visited](PackageDecl* src, std::string_view name) {
                      auto sub = visited;
                      LowerImportedName(src, name, sub);
                    }};
  for (auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kExportDecl) continue;
    HandleReExport(walk, item->import_item);
  }
}

static void AliasPackageDataItem(const PackageDecl* pkg, const ModuleItem* item,
                                 SimContext& ctx) {
  bool is_param = item->kind == ModuleItemKind::kParamDecl;
  bool is_var = item->kind == ModuleItemKind::kVarDecl;
  if (!(is_param || is_var) || !item->init_expr) return;
  if (ctx.FindVariable(item->name)) return;
  std::string qname = std::string(pkg->name) + "." + std::string(item->name);
  ctx.AliasVariable(item->name, qname);
}

static void AliasAllPackageDataItems(const PackageDecl* pkg, SimContext& ctx) {
  for (const auto* item : pkg->items) AliasPackageDataItem(pkg, item, ctx);
}

static void AliasNamedPackageDataItem(const PackageDecl* pkg,
                                      std::string_view item_name,
                                      SimContext& ctx) {
  for (const auto* item : pkg->items) {
    if (item->name == item_name) AliasPackageDataItem(pkg, item, ctx);
  }
}

void Lowerer::LowerImports(const RtlirModule* mod) {
  auto apply_import = [&](const RtlirImport& imp) {
    auto* pkg = FindPackage(imp.package_name);
    if (!pkg) return;
    std::unordered_set<const PackageDecl*> visited;
    if (imp.is_wildcard) {
      LowerAllImported(pkg, visited);
      AliasAllPackageDataItems(pkg, ctx_);
    } else {
      LowerImportedName(pkg, imp.item_name, visited);
      AliasNamedPackageDataItem(pkg, imp.item_name, ctx_);
    }
  };

  // §26.5: an explicit import of a name takes precedence over a wildcard import
  // of the same name. Because alias_data_item lets the first binding of a name
  // win, the explicitly imported names must be bound before any wildcard import
  // is applied, regardless of the order the import declarations appear in the
  // source. Module-local declarations are materialized before LowerImports
  // runs, so they already shadow both kinds of import.
  for (const auto& imp : mod->imports)
    if (!imp.is_wildcard) apply_import(imp);
  for (const auto& imp : mod->imports)
    if (imp.is_wildcard) apply_import(imp);
}

}  // namespace delta
