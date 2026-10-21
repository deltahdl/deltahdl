#include "elaborator/nettype_registration.h"

#include <string>
#include <string_view>
#include <unordered_set>

#include "common/arena.h"
#include "elaborator/nettype_resolution_lookup.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

std::string ScopedKey(std::string_view scope, std::string_view name) {
  return std::string(scope) + "::" + std::string(name);
}

// The name of the function `item`'s with clause names, qualified by the scope
// declaring it: the scope the clause writes, or, for a bare name, `home`, the
// package declaring the nettype, as the package's declarations see each
// other by their bare names.
std::string_view ResolveFuncName(const ModuleItem& item, std::string_view home,
                                 Arena& arena) {
  const std::string kScope = item.nettype_resolve_scope != nullptr
                                 ? NettypeScopeText(*item.nettype_resolve_scope)
                                 : std::string(home);
  if (kScope.empty()) return item.nettype_resolve_func;
  return *arena.Create<std::string>(
      ScopedKey(kScope, item.nettype_resolve_func));
}

// The key the type `source` names would be recorded under were it a nettype.
// A.2.1.3 lets a renamed nettype be written through a package, "P::nt"; a bare
// name in a package is one of `home`'s own nettypes when it declares one of
// that name; and any other bare name is its own key.
std::string SourceKey(const DataType& source, std::string_view home,
                      const std::unordered_set<std::string_view>& names) {
  if (!source.scope_name.empty())
    return ScopedKey(source.scope_name, source.type_name);
  if (!home.empty()) {
    std::string in_home = ScopedKey(home, source.type_name);
    if (names.count(in_home) != 0) return in_home;
  }
  return std::string(source.type_name);
}

// The data type of a nettype package `pkg` declares. A bare name that `pkg`
// declares is written through `pkg`: a typedef's name as InPackageScope writes
// it, and that of a nettype the declaration renames.
DataType InPackageNettypeScope(
    const DataType& type, const PackageDecl& pkg,
    const std::unordered_set<std::string_view>& names) {
  DataType scoped = InPackageScope(type, pkg);
  if (scoped.kind == DataTypeKind::kNamed && scoped.scope_name.empty() &&
      names.count(ScopedKey(pkg.name, scoped.type_name)) != 0)
    scoped.scope_name = pkg.name;
  return scoped;
}

}  // namespace

void RegisterNettype(const ModuleItem& item, std::string_view key,
                     std::string_view home, const NettypeTables& tables,
                     Arena& arena) {
  tables.canonical[key] = key;
  if (!item.nettype_resolve_func.empty()) {
    tables.resolve_funcs[key] = ResolveFuncName(item, home, arena);
    return;
  }
  if (item.typedef_type.kind != DataTypeKind::kNamed) return;
  const std::string kSource = SourceKey(item.typedef_type, home, tables.names);
  if (tables.names.count(kSource) == 0) return;
  auto fit = tables.resolve_funcs.find(kSource);
  if (fit != tables.resolve_funcs.end())
    tables.resolve_funcs[key] = fit->second;
  auto cit = tables.canonical.find(kSource);
  if (cit != tables.canonical.end()) tables.canonical[key] = cit->second;
}

void CopyNettype(std::string_view from, std::string_view to,
                 TypedefMap& typedefs, const NettypeTables& tables) {
  auto td = typedefs.find(from);
  if (td == typedefs.end()) return;
  typedefs[to] = td->second;
  tables.names.insert(to);
  auto fit = tables.resolve_funcs.find(from);
  if (fit != tables.resolve_funcs.end()) tables.resolve_funcs[to] = fit->second;
  auto cit = tables.canonical.find(from);
  if (cit != tables.canonical.end()) tables.canonical[to] = cit->second;
}

void RegisterPackageNettypes(const CompilationUnit* unit, TypedefMap& typedefs,
                             const NettypeTables& tables, Arena& arena) {
  for (const PackageDecl* pkg : unit->packages) {
    for (const ModuleItem* item : pkg->items) {
      if (item->kind != ModuleItemKind::kNettypeDecl) continue;
      std::string_view key =
          *arena.Create<std::string>(ScopedKey(pkg->name, item->name));
      typedefs[key] =
          InPackageNettypeScope(item->typedef_type, *pkg, tables.names);
      tables.names.insert(key);
      RegisterNettype(*item, key, pkg->name, tables, arena);
    }
  }
}

}  // namespace delta
