#include "elaborator/type_site_lookup.h"

#include <cstddef>
#include <string_view>
#include <vector>

#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// The name the item `item` declares, a class's being its declaration's.
std::string_view DeclaredName(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kClassDecl ? item.class_decl->name
                                                 : item.name;
}

// The last item of kind `kind` among the items of the site `site` declaring
// `name`, a forward typedef (§6.18), which names no type, excepted.
FoundItem ItemBefore(const TypeSite& site, ModuleItemKind kind,
                     std::string_view name) {
  FoundItem found;
  for (std::size_t i = 0; i < site.end; ++i) {
    const ModuleItem& item = *(*site.items)[i];
    if (item.kind == kind && DeclaredName(item) == name &&
        item.forward_type_kind == DataTypeKind::kImplicit) {
      found = {&item, {site.items, i, site.kind, site.outer}};
    }
  }
  return found;
}

// §26.2: the item of kind `kind` the package `package` of the compilation unit
// declares under `name`.
FoundItem PackageItem(const CompilationUnit& unit, std::string_view package,
                      ModuleItemKind kind, std::string_view name) {
  FoundItem found;
  for (const PackageDecl* decl : unit.packages) {
    if (decl->name == package) {
      found = ItemBefore({&decl->items, decl->items.size(), SiteKind::kPackage},
                         kind, name);
    }
  }
  return found;
}

// §26.3: the item of kind `kind` named `name` an import among the first `end`
// of `items` brings in, by its item name or with a wildcard.
FoundItem ImportedItem(const CompilationUnit& unit,
                       const std::vector<ModuleItem*>& items, std::size_t end,
                       ModuleItemKind kind, std::string_view name) {
  FoundItem found;
  for (std::size_t i = 0; i < end; ++i) {
    if (items[i]->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& import = items[i]->import_item;
    if (!import.is_wildcard && import.item_name != name) continue;
    const FoundItem kHit = PackageItem(unit, import.package_name, kind, name);
    if (kHit.item != nullptr) found = kHit;
  }
  return found;
}

// §23.9 with §26.3: the item of kind `kind` named `name` the site `site` sees:
// one its scope declares, else one an import of its scope brings in, else,
// for a generate block, one the scope around it sees (§27.5), else, for a
// module, one the compilation unit declares or imports.
FoundItem SiteItem(const CompilationUnit& unit, const TypeSite& site,
                   ModuleItemKind kind, std::string_view name) {
  FoundItem found = ItemBefore(site, kind, name);
  if (found.item == nullptr) {
    found = ImportedItem(unit, *site.items, site.end, kind, name);
  }
  if (found.item == nullptr && site.outer != nullptr) {
    return SiteItem(unit, *site.outer, kind, name);
  }
  if (found.item == nullptr && site.kind == SiteKind::kModule) {
    const TypeSite kUnit{&unit.cu_items, unit.cu_items.size(), SiteKind::kUnit};
    found = SiteItem(unit, kUnit, kind, name);
  }
  return found;
}

}  // namespace

const ClassDecl* ClassIn(const CompilationUnit& unit, const TypeSite& site,
                         std::string_view name) {
  const TypeSite kWhole{site.items, site.items->size(), site.kind, site.outer};
  const FoundItem kFound =
      SiteItem(unit, kWhole, ModuleItemKind::kClassDecl, name);
  if (kFound.item != nullptr) return kFound.item->class_decl;
  if (site.kind == SiteKind::kPackage) return nullptr;
  for (const ClassDecl* decl : unit.classes) {
    if (decl->name == name) return decl;
  }
  return nullptr;
}

const ClassDecl* ScopedClass(const CompilationUnit& unit, const TypeSite& site,
                             std::string_view scope_name,
                             std::string_view name) {
  const FoundItem kInPackage =
      PackageItem(unit, scope_name, ModuleItemKind::kClassDecl, name);
  if (kInPackage.item != nullptr) return kInPackage.item->class_decl;
  const ClassDecl* outer = ClassIn(unit, site, scope_name);
  if (outer == nullptr) return nullptr;
  for (const ClassMember* member : outer->members) {
    if (member->nested_class != nullptr && member->nested_class->name == name) {
      return member->nested_class;
    }
  }
  return nullptr;
}

FoundItem TypedefOf(const CompilationUnit& unit, const TypeSite& site,
                    const DataType& type) {
  if (!type.scope_name.empty()) {
    return PackageItem(unit, type.scope_name, ModuleItemKind::kTypedef,
                       type.type_name);
  }
  return SiteItem(unit, site, ModuleItemKind::kTypedef, type.type_name);
}

}  // namespace delta
