#include <functional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
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

// The key SimContext holds package `pkg`'s class `cls` under for a reference
// through the package scope resolution operator (§26.3), spelled as the source
// spells it. The evaluator builds the same key from `p::C` in
// ResolveClassScope (src/simulator/eval_function.cpp).
static std::string_view QualifiedClassKey(const PackageDecl* pkg,
                                          const ClassDecl* cls, Arena& arena) {
  auto* key = arena.Create<std::string>(std::string(pkg->name) +
                                        "::" + std::string(cls->name));
  return *key;
}

void Lowerer::LowerPackageClass(const PackageDecl* pkg, const ClassDecl* cls) {
  std::string_view key = QualifiedClassKey(pkg, cls, arena_);
  if (ctx_.FindClassType(key)) return;
  LowerClassDecl(cls, pkg->items);
  ctx_.RegisterClassType(key, ctx_.FindClassType(cls->name));
}

void Lowerer::LowerPackageItem(const PackageDecl* pkg, ModuleItem* item) {
  if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
    // §26.5: a declaration of the importing scope, or an earlier import, has
    // already bound the bare name and keeps it.
    if (ctx_.FindClassType(item->class_decl->name)) return;
    ClassTypeInfo* lowered =
        ctx_.FindClassType(QualifiedClassKey(pkg, item->class_decl, arena_));
    if (lowered) {
      ctx_.RegisterClassType(item->class_decl->name, lowered);
    } else {
      LowerPackageClass(pkg, item->class_decl);
    }
  } else if (item->kind == ModuleItemKind::kFunctionDecl ||
             item->kind == ModuleItemKind::kTaskDecl) {
    // §8.24: an out-of-block method body is the class's, not a subroutine of
    // the package; LowerPackageClass attaches it to the class.
    if (!item->method_class.empty()) return;
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

void Lowerer::LowerImportedName(
    PackageDecl* pkg, std::string_view name,
    std::unordered_set<const PackageDecl*>& visited) {
  if (!visited.insert(pkg).second) return;
  if (auto* found = FindNamedPackageItem(pkg, name)) {
    LowerPackageItem(pkg, found);
    // §26.6: an `export pkg::name` makes the given declaration available to a
    // downstream import following the same rules as a direct import. When that
    // declaration is a parameter or variable, its downstream visibility comes
    // from aliasing the unqualified name to the qualified name in the package
    // that declares it. LowerPackageItem only handles subroutines/classes, so
    // alias the data item here from `pkg` -- the origin package where `found`
    // is declared -- so a re-exported constant/variable resolves at runtime.
    AliasPackageDataItem(pkg, found);
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
    LowerPackageItem(pkg, item);
    // §26.6: mirror the named-import path -- a data declaration reached by
    // lowering all of a (possibly re-exported) package must also be aliased
    // from this package so a wildcard consumer of a re-exported constant or
    // variable can resolve it at runtime.
    AliasPackageDataItem(pkg, item);
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

void Lowerer::AliasPackageDataItem(const PackageDecl* pkg,
                                   const ModuleItem* item) {
  bool is_param = item->kind == ModuleItemKind::kParamDecl;
  bool is_var = item->kind == ModuleItemKind::kVarDecl;
  if (!(is_param || is_var) || !item->init_expr) return;
  // §26.3 makes the imported name visible "within the current scope", and the
  // current scope is the one that wrote the import. Key the binding by the
  // instance being lowered so two instances importing a like-named item from
  // two different packages each read their own, which §26.3 permits: the only
  // conflict it rules illegal is between wildcard imports "within the same
  // scope". The prefix is empty for a top module, where the key is the bare
  // name and SimContext::FindVariable's ordinary lookup answers it.
  std::string key = inst_prefix_ + std::string(item->name);
  // §26.5: a declaration of the importing scope shadows the import, and the
  // first import of a name wins over a later one. Both are already bound under
  // this key, so an occupied key is left alone. The map is read directly rather
  // than through SimContext::FindVariable, which would also answer from an
  // enclosing scope's binding and let one module's import silence another's.
  if (ctx_.GetVariables().count(key) != 0) return;
  std::string qname = std::string(pkg->name) + "." + std::string(item->name);
  auto* stored = arena_.Create<std::string>(key);
  ctx_.AliasVariable(*stored, qname);
  // §26.3: the import makes this name visible under its unqualified spelling,
  // and that binding belongs to no module. SimContext::FindVariable is told so
  // because it otherwise stops a bare name at the module boundary §23.9 draws,
  // which would hide an imported item from inside every instance.
  ctx_.RegisterImportedName(*stored);
}

void Lowerer::AliasAllPackageDataItems(const PackageDecl* pkg) {
  for (const auto* item : pkg->items) AliasPackageDataItem(pkg, item);
}

void Lowerer::AliasNamedPackageDataItem(const PackageDecl* pkg,
                                        std::string_view item_name) {
  for (const auto* item : pkg->items) {
    if (item->name == item_name) AliasPackageDataItem(pkg, item);
  }
}

void Lowerer::LowerOneImport(const ImportItem& imp) {
  auto* pkg = FindPackage(imp.package_name);
  if (!pkg) return;
  std::unordered_set<const PackageDecl*> visited;
  if (imp.is_wildcard) {
    LowerAllImported(pkg, visited);
    AliasAllPackageDataItems(pkg);
  } else {
    LowerImportedName(pkg, imp.item_name, visited);
    AliasNamedPackageDataItem(pkg, imp.item_name);
  }
}

void Lowerer::LowerImports(const RtlirModule* mod) {
  auto apply_import = [&](const RtlirImport& imp) {
    ImportItem item;
    item.package_name = imp.package_name;
    item.item_name = imp.item_name;
    item.is_wildcard = imp.is_wildcard;
    LowerOneImport(item);
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

void Lowerer::LowerCompilationUnitImports() {
  if (!design_ || !design_->compilation_unit) return;
  const auto& items = design_->compilation_unit->cu_items;
  // §26.5's precedence of an explicit import over a wildcard one holds in the
  // compilation-unit scope as in a module, so the explicit imports bind first.
  for (const auto* item : items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (!item->import_item.is_wildcard) LowerOneImport(item->import_item);
  }
  for (const auto* item : items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (item->import_item.is_wildcard) LowerOneImport(item->import_item);
  }
}

void Lowerer::LowerUnimportedClassesOf(const PackageDecl* pkg) {
  // LowerClassDecl binds the bare name while it lowers, and a class of the
  // package that extends an earlier one resolves its base through that
  // binding (§8.13), so the bare names are left in place until the whole
  // package is done and only then given back to whatever held them before: a
  // declaration or an import of a scope that this pass must not displace
  // (§26.5). A bare name nothing held stays bound to the package's class.
  std::vector<std::pair<std::string_view, ClassTypeInfo*>> displaced;
  for (const auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kClassDecl || !item->class_decl) continue;
    const ClassDecl* cls = item->class_decl;
    if (ctx_.FindClassType(QualifiedClassKey(pkg, cls, arena_))) continue;
    if (ClassTypeInfo* held = ctx_.FindClassType(cls->name))
      displaced.emplace_back(cls->name, held);
    LowerPackageClass(pkg, cls);
  }
  for (const auto& [name, held] : displaced) ctx_.RegisterClassType(name, held);
}

void Lowerer::LowerUnimportedPackageClasses() {
  if (!design_) return;
  for (const auto* pkg : design_->packages) LowerUnimportedClassesOf(pkg);
}

}  // namespace delta
