#include "elaborator/nettype_resolution_lookup.h"

#include <cstddef>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// The function a class declares under `name`, whether or not it is static.
// §6.6.7 admits a non-static one as far as being found, and rejects it by the
// class-static rule rather than by not finding it, which is what lets the
// report say what is wrong with the source rather than that the name is
// missing.
NettypeResolutionTarget ClassResolutionMethod(const ClassDecl* cls,
                                              std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
    if (m->method->name != name) continue;
    return {m->method, true, m->is_static, false};
  }
  return {nullptr, true, false, false};
}

// The function among `items`, a package's or the compilation unit's, declared
// under `name`.
const ModuleItem* FunctionAmong(const std::vector<ModuleItem*>& items,
                                std::string_view name) {
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == name)
      return item;
  }
  return nullptr;
}

// The package `unit` declares under `name`, or null.
const PackageDecl* FindNettypeScopePackage(const CompilationUnit* unit,
                                           std::string_view name) {
  for (const auto* p : unit->packages) {
    if (p->name == name) return p;
  }
  return nullptr;
}

// The class the scope of a resolution function names: a class by its own name,
// or one a typedef names, which §6.6.7's own example does with `typedef
// Base#(32) MyBaseT;` and `with MyBaseT::Ssum` (printed page 99). A chain of
// typedefs is followed to the class; the hop limit keeps a cyclic typedef from
// looping.
const ClassDecl* NettypeScopeClass(std::string_view scope,
                                   const CompilationUnit* unit,
                                   const TypedefMap& typedefs) {
  for (int hops = 0; hops < 8; ++hops) {
    if (const ClassDecl* cls = FindClassDecl(scope, unit)) return cls;
    auto td = typedefs.find(scope);
    if (td == typedefs.end() || td->second.kind != DataTypeKind::kNamed)
      return nullptr;
    scope = td->second.type_name;
  }
  return nullptr;
}

// The class `$unit::name` names (§3.12.1): one the compilation unit declares,
// or, where it declares none of the name, a typedef naming a class.
const ClassDecl* UnitScopeClass(std::string_view name,
                                const CompilationUnit* unit,
                                const TypedefMap& typedefs) {
  for (const auto* cls : unit->classes) {
    if (cls->name == name) return cls;
  }
  if (typedefs.count(name) == 0) return nullptr;
  return NettypeScopeClass(name, unit, typedefs);
}

// The names of `scope`, outermost first, ending in the one declaring the
// function.
std::vector<std::string_view> ScopeNames(const DataType& scope) {
  std::vector<std::string_view> names(scope.outer_scope_names.begin(),
                                      scope.outer_scope_names.end());
  if (!scope.scope_name.empty()) names.push_back(scope.scope_name);
  names.push_back(scope.type_name);
  return names;
}

// `cls` followed down the classes nested in it (§8.23) that `names` writes
// from `next` on, or null where one of them is not declared there.
const ClassDecl* NestedClassAlong(const ClassDecl* cls,
                                  const std::vector<std::string_view>& names,
                                  size_t next) {
  for (; cls != nullptr && next < names.size(); ++next) {
    cls = FindNestedClass(cls, names[next]);
  }
  return cls;
}

// The class a scope of two names or more reaches. A.2.2.1's class_type opens
// with a ps_class_identifier, so the first name is `$unit` or a package the
// second class is declared in, or else is itself the class, and every name
// after that is a class nested in the one before.
const ClassDecl* NettypeScopeChainClass(
    const std::vector<std::string_view>& names, const CompilationUnit* unit,
    const TypedefMap& typedefs) {
  if (names[0] == "$unit") {
    return NestedClassAlong(UnitScopeClass(names[1], unit, typedefs), names, 2);
  }
  if (const ClassDecl* in_package =
          FindClassInPackage(names[0], names[1], unit)) {
    return NestedClassAlong(in_package, names, 2);
  }
  return NestedClassAlong(NettypeScopeClass(names[0], unit, typedefs), names,
                          1);
}

}  // namespace

NettypeResolutionTarget FindNettypeResolutionFunction(
    const ModuleItem* item, const CompilationUnit* unit,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const TypedefMap& typedefs) {
  const std::string_view kName = item->nettype_resolve_func;
  if (item->nettype_resolve_scope == nullptr) {
    auto fit = func_decls.find(kName);
    if (fit == func_decls.end()) return {};
    return {fit->second, false, false, false};
  }
  const std::vector<std::string_view> kNames =
      ScopeNames(*item->nettype_resolve_scope);
  if (kNames.size() > 1) {
    const ClassDecl* cls = NettypeScopeChainClass(kNames, unit, typedefs);
    if (cls == nullptr) return {nullptr, false, false, true};
    return ClassResolutionMethod(cls, kName);
  }
  if (kNames[0] == "$unit") {
    return {FunctionAmong(unit->cu_items, kName), false, false, false};
  }
  if (const ClassDecl* cls = NettypeScopeClass(kNames[0], unit, typedefs))
    return ClassResolutionMethod(cls, kName);
  if (const PackageDecl* pkg = FindNettypeScopePackage(unit, kNames[0]))
    return {FunctionAmong(pkg->items, kName), false, false, false};
  return {nullptr, false, false, true};
}

std::string NettypeScopeText(const DataType& scope) {
  std::string text;
  for (std::string_view name : ScopeNames(scope)) {
    if (!text.empty()) text += "::";
    text += name;
  }
  return text;
}

}  // namespace delta
