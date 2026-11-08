#include <algorithm>
#include <cstddef>
#include <format>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

using TypeSubst = std::unordered_map<std::string_view, DataType>;

static DataType ResolveType(const DataType& type, const TypeSubst& subst) {
  if (type.type_name.empty()) return type;
  auto it = subst.find(type.type_name);
  return it == subst.end() ? type : it->second;
}

static bool MethodSignaturesCompatible(const ModuleItem* a,
                                       const TypeSubst& a_subst,
                                       const ModuleItem* b,
                                       const TypeSubst& b_subst) {
  if (!TypesMatch(ResolveType(a->return_type, a_subst),
                  ResolveType(b->return_type, b_subst)))
    return false;
  if (a->func_args.size() != b->func_args.size()) return false;
  for (size_t i = 0; i < a->func_args.size(); ++i) {
    if (!TypesMatch(ResolveType(a->func_args[i].data_type, a_subst),
                    ResolveType(b->func_args[i].data_type, b_subst)))
      return false;
    if (a->func_args[i].direction != b->func_args[i].direction) return false;
  }
  return true;
}

static std::string MakeSpecKey(std::string_view name,
                               const std::vector<DataType>& type_params,
                               const ScopeMap& scope) {
  if (type_params.empty()) return std::string(name);
  std::string key(name);
  key += "#(";
  for (size_t i = 0; i < type_params.size(); ++i) {
    if (i > 0) key += ',';
    const auto& dt = type_params[i];
    if (!dt.type_name.empty()) {
      key += dt.type_name;
    } else if (dt.type_ref_expr != nullptr) {
      if (auto v = ConstEvalInt(dt.type_ref_expr, scope))
        key += 'v' + std::to_string(*v);
      else
        key += "v?";
    } else {
      key += std::to_string(static_cast<int>(dt.kind));
    }
  }
  key += ')';
  return key;
}

struct IfaceSpec {
  std::string key;
  TypeSubst subst;
};

struct ClassLookup {
  const CompilationUnit* unit;
  const ScopeMap& params;
};

using IfaceMethodMap =
    std::unordered_map<std::string_view,
                       std::vector<std::pair<IfaceSpec, const ModuleItem*>>>;

static std::vector<std::string_view> TypeParamNames(const ClassDecl* cls) {
  std::vector<std::string_view> names;
  for (const auto& [pname, _] : cls->params) {
    if (cls->type_param_names.count(pname) != 0) names.push_back(pname);
  }
  return names;
}

static IfaceSpec MakeIfaceSpec(const ClassDecl* iface, std::string_view name,
                               const std::vector<DataType>& args,
                               const TypeSubst& outer, const ScopeMap& scope) {
  std::vector<DataType> resolved;
  resolved.reserve(args.size());
  for (const auto& arg : args) resolved.push_back(ResolveType(arg, outer));
  IfaceSpec spec;
  spec.key = MakeSpecKey(name, resolved, scope);
  auto formals = TypeParamNames(iface);
  for (size_t i = 0; i < formals.size() && i < resolved.size(); ++i) {
    spec.subst.emplace(formals[i], resolved[i]);
  }
  return spec;
}

static void ForEachInterfaceParent(
    const ClassDecl* cls, const ClassLookup& look,
    const std::function<void(const ClassDecl*, std::string_view,
                             const std::vector<DataType>&)>& fn);

static void CollectInterfacePureVirtualMethods(
    const ClassDecl* iface, const IfaceSpec& spec, const ClassLookup& look,
    IfaceMethodMap& out, std::unordered_set<std::string>& visited) {
  if (!visited.insert(spec.key).second) return;
  for (const auto* m : iface->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->is_pure_virtual) continue;
    if (!m->method) continue;
    out[m->method->name].push_back({spec, m->method});
  }
  ForEachInterfaceParent(
      iface, look,
      [&](const ClassDecl* parent, std::string_view name,
          const std::vector<DataType>& args) {
        CollectInterfacePureVirtualMethods(
            parent, MakeIfaceSpec(parent, name, args, spec.subst, look.params),
            look, out, visited);
      });
}

static void CollectImplementedInterfaces(const ClassDecl* cls,
                                         const CompilationUnit* unit,
                                         std::vector<InterfaceRef>& out) {
  for (const auto& iface : cls->implements_types) {
    out.push_back(iface);
  }
  if (!cls->base_class.empty()) {
    const auto* base = FindBaseClass(cls, unit);
    if (base && !base->is_interface) {
      CollectImplementedInterfaces(base, unit, out);
    }
  }
}

static void CollectInScopeInterfaceMethods(const ClassDecl* cls,
                                           const ClassLookup& look,
                                           IfaceMethodMap& iface_methods) {
  std::unordered_set<std::string> visited;
  TypeSubst outer;
  if (cls->is_interface) {
    ForEachInterfaceParent(
        cls, look,
        [&](const ClassDecl* parent, std::string_view name,
            const std::vector<DataType>& args) {
          CollectInterfacePureVirtualMethods(
              parent, MakeIfaceSpec(parent, name, args, outer, look.params),
              look, iface_methods, visited);
        });
  } else {
    std::vector<InterfaceRef> all_ifaces;
    CollectImplementedInterfaces(cls, look.unit, all_ifaces);
    std::unordered_set<std::string> seen_iface;
    for (const auto& iref : all_ifaces) {
      const auto* iface = FindReferencedClass(iref, look.unit);
      if (!iface || !iface->is_interface) continue;
      auto spec =
          MakeIfaceSpec(iface, iref.name, iref.type_params, outer, look.params);
      if (!seen_iface.insert(spec.key).second) continue;
      CollectInterfacePureVirtualMethods(iface, spec, look, iface_methods,
                                         visited);
    }
  }
}

static std::string_view InterfaceClassOfSpecKey(std::string_view key) {
  return key.substr(0, key.find("#("));
}

static Subclause ConflictSubclause(const std::vector<std::string_view>& keys,
                                   Subclause unrelated) {
  for (auto key : keys) {
    if (InterfaceClassOfSpecKey(key) != InterfaceClassOfSpecKey(keys.front()))
      return unrelated;
  }
  return Subclause("8.26.6.3");
}

static void DiagnoseInterfaceSignatureConflicts(
    const ClassDecl* cls, const IfaceMethodMap& iface_methods,
    DiagEngine& diag) {
  for (const auto& [method_name, entries] : iface_methods) {
    if (entries.size() < 2) continue;
    if (method_name == "pre_randomize" || method_name == "post_randomize")
      continue;
    const auto* first_method = entries[0].second;
    for (size_t i = 1; i < entries.size(); ++i) {
      if (!MethodSignaturesCompatible(first_method, entries[0].first.subst,
                                      entries[i].second,
                                      entries[i].first.subst)) {
        diag.Error(
            cls->range.start,
            std::format("method name conflict for '{}' in '{}': incompatible "
                        "signatures in interface '{}' and interface '{}'",
                        method_name, cls->name, entries[0].first.key,
                        entries[i].first.key),
            ConflictSubclause({entries[0].first.key, entries[i].first.key},
                              Subclause("8.26.6.1")));
        break;
      }
    }
  }
}

static const ModuleItem* FindVirtualMethodInBaseChain(
    const ClassDecl* cls, std::string_view method_name,
    const CompilationUnit* unit, bool require_non_pure) {
  for (const auto* walk = FindBaseClass(cls, unit); walk;
       walk = FindBaseClass(walk, unit)) {
    for (const auto* bm : walk->members) {
      if (bm->kind == ClassMemberKind::kMethod && bm->method &&
          bm->method->name == method_name && bm->is_virtual &&
          (!require_non_pure || !bm->is_pure_virtual)) {
        return bm->method;
      }
    }
  }
  return nullptr;
}

static const ModuleItem* FindMethodNameConflictImpl(
    const ClassDecl* cls, std::string_view method_name,
    const CompilationUnit* unit) {
  for (const auto* cm : cls->members) {
    if (cm->kind == ClassMemberKind::kMethod && cm->method &&
        cm->method->name == method_name &&
        (cm->is_virtual || cm->is_pure_virtual)) {
      return cm->method;
    }
  }
  return FindVirtualMethodInBaseChain(cls, method_name, unit, false);
}

static void DiagnoseImplSignatureMismatches(const ClassDecl* cls,
                                            const IfaceMethodMap& iface_methods,
                                            const CompilationUnit* unit,
                                            DiagEngine& diag) {
  for (const auto& [method_name, entries] : iface_methods) {
    const ModuleItem* impl = FindMethodNameConflictImpl(cls, method_name, unit);
    if (!impl) continue;
    const TypeSubst kImplSubst;
    for (const auto& [iface_spec, iface_method] : entries) {
      if (!MethodSignaturesCompatible(impl, kImplSubst, iface_method,
                                      iface_spec.subst)) {
        diag.Error(impl->loc,
                   std::format("method '{}' does not match signature of pure "
                               "virtual method '{}' in interface '{}'",
                               method_name, method_name, iface_spec.key),
                   Subclause("8.26.6.1"));
        break;
      }
    }
  }
}

static void ValidateMethodNameConflicts(const ClassDecl* cls,
                                        const ClassLookup& look,
                                        DiagEngine& diag) {
  IfaceMethodMap iface_methods;
  CollectInScopeInterfaceMethods(cls, look, iface_methods);
  DiagnoseInterfaceSignatureConflicts(cls, iface_methods, diag);
  if (!cls->is_interface) {
    DiagnoseImplSignatureMismatches(cls, iface_methods, look.unit, diag);
  }
}

static const ModuleItem* FindConcreteMethodInHierarchy(
    const ClassDecl* cls, std::string_view method_name,
    const CompilationUnit* unit) {
  for (const auto* cm : cls->members) {
    if (cm->kind == ClassMemberKind::kMethod && cm->method &&
        cm->method->name == method_name && cm->is_virtual) {
      return cm->method;
    }
  }
  return FindVirtualMethodInBaseChain(cls, method_name, unit, true);
}

static void CheckImplInterfaceArgDefaults(const ModuleItem* iface_method,
                                          const ModuleItem* impl,
                                          std::string_view iface_name,
                                          const ScopeMap& param_scope,
                                          DiagEngine& diag) {
  const auto& iface_args = iface_method->func_args;
  const auto& impl_args = impl->func_args;
  size_t n = std::min(iface_args.size(), impl_args.size());
  for (size_t i = 0; i < n; ++i) {
    bool iface_has = iface_args[i].default_value != nullptr;
    bool impl_has = impl_args[i].default_value != nullptr;
    if (iface_has != impl_has) {
      diag.Error(impl->loc,
                 std::format("method '{}' argument '{}': default value "
                             "presence does not match interface '{}'",
                             impl->name, impl_args[i].name, iface_name),
                 Subclause("8.26.8"));
      continue;
    }
    if (!iface_has) continue;
    auto iface_val = ConstEvalInt(iface_args[i].default_value, param_scope);
    auto impl_val = ConstEvalInt(impl_args[i].default_value, param_scope);
    if (iface_val && impl_val && *iface_val != *impl_val) {
      diag.Error(impl->loc,
                 std::format("method '{}' argument '{}': default value "
                             "does not match interface '{}' (expected {}, "
                             "got {})",
                             impl->name, impl_args[i].name, iface_name,
                             *iface_val, *impl_val),
                 Subclause("8.26.8"));
    }
  }
}

struct ImplementedInterface {
  const ClassDecl* decl;
  std::string_view name;
};

static void CheckInterfaceMethods(const ClassDecl* cls,
                                  const ImplementedInterface& iface,
                                  const CompilationUnit* unit,
                                  const ScopeMap& param_scope,
                                  DiagEngine& diag) {
  for (const auto* im : iface.decl->members) {
    if (im->kind != ClassMemberKind::kMethod || !im->is_pure_virtual) continue;
    if (!im->method) continue;
    const auto* impl =
        FindConcreteMethodInHierarchy(cls, im->method->name, unit);
    if (!impl) {
      diag.Error(cls->range.start,
                 std::format("class '{}' does not implement pure virtual "
                             "method '{}' from interface '{}'",
                             cls->name, im->method->name, iface.name),
                 Subclause("8.26"));
      continue;
    }
    CheckImplInterfaceArgDefaults(im->method, impl, iface.name, param_scope,
                                  diag);
  }
}

void ElaboratorClassRules::ValidateImplementsInterfaceMethods(
    const ClassDecl* cls) {
  if (cls->is_virtual) return;
  std::vector<InterfaceRef> all_ifaces;
  CollectImplementedInterfaces(cls, unit_, all_ifaces);
  if (all_ifaces.empty()) return;
  std::unordered_set<std::string> seen;
  for (const auto& iref : all_ifaces) {
    auto iface_key = MakeSpecKey(iref.name, iref.type_params, cu_param_scope_);
    if (!seen.insert(iface_key).second) continue;
    const auto* iface = FindReferencedClass(iref, unit_);
    if (!iface || !iface->is_interface) continue;
    CheckInterfaceMethods(cls, {iface, iref.name}, unit_, cu_param_scope_,
                          diag_);
  }
}

static bool VirtualClassAddressesPrototype(const ClassDecl* cls,
                                           std::string_view method_name,
                                           const CompilationUnit* unit) {
  for (const auto* walk = cls; walk; walk = FindBaseClass(walk, unit)) {
    for (const auto* m : walk->members) {
      if (m->kind == ClassMemberKind::kMethod && m->method &&
          m->method->name == method_name &&
          (m->is_virtual || m->is_pure_virtual)) {
        return true;
      }
    }
  }
  return false;
}

void ElaboratorClassRules::ValidateVirtualClassInterfaceObligations(
    const ClassDecl* cls, const ScopeMap& params) {
  if (!cls->is_virtual || cls->is_interface || cls->implements_types.empty())
    return;
  std::unordered_set<std::string> seen_iface;
  TypeSubst outer;
  ClassLookup look{unit_, params};
  for (const auto& iref : cls->implements_types) {
    const auto* iface = FindReferencedClass(iref, unit_);
    if (!iface || !iface->is_interface) continue;
    auto spec =
        MakeIfaceSpec(iface, iref.name, iref.type_params, outer, params);
    if (!seen_iface.insert(spec.key).second) continue;
    IfaceMethodMap iface_methods;
    std::unordered_set<std::string> visited;
    CollectInterfacePureVirtualMethods(iface, spec, look, iface_methods,
                                       visited);
    for (const auto& entry : iface_methods) {
      std::string_view method_name = entry.first;
      if (!VirtualClassAddressesPrototype(cls, method_name, unit_)) {
        diag_.Error(
            cls->range.start,
            std::format("virtual class '{}' implements interface '{}' but "
                        "neither implements nor re-declares as pure virtual "
                        "the method '{}'",
                        cls->name, iref.name, method_name),
            Subclause("8.26.7"));
      }
    }
  }
}

using NameOriginMap =
    std::unordered_map<std::string_view, std::unordered_set<std::string>>;

static void CollectOwnParamTypeNames(
    const ClassDecl* iface, std::unordered_set<std::string_view>& own_names) {
  for (const auto& [pname, _] : iface->params) own_names.insert(pname);
  for (const auto* m : iface->members) {
    if (m->kind == ClassMemberKind::kTypedef ||
        m->kind == ClassMemberKind::kProperty)
      own_names.insert(m->name);
  }
}

static void ForEachInterfaceParent(
    const ClassDecl* cls, const ClassLookup& look,
    const std::function<void(const ClassDecl*, std::string_view,
                             const std::vector<DataType>&)>& fn) {
  if (!cls->base_class.empty()) {
    const auto* base = FindBaseClass(cls, look.unit);
    if (base && base->is_interface) {
      fn(base, cls->base_class, cls->base_class_type_params);
    }
  }
  for (const auto& ref : cls->extends_interfaces) {
    const auto* ext = FindReferencedClass(ref, look.unit);
    if (ext && ext->is_interface) {
      fn(ext, ref.name, ref.type_params);
    }
  }
}

static void CollectEffectiveParamTypeNames(const ClassDecl* iface,
                                           const std::string& spec_key,
                                           const ClassLookup& look,
                                           NameOriginMap& out);

static void MergeInheritedParamTypeNames(
    const ClassDecl* parent, const std::string& parent_key,
    const ClassLookup& look,
    const std::unordered_set<std::string_view>& own_names, NameOriginMap& out) {
  NameOriginMap parent_map;
  CollectEffectiveParamTypeNames(parent, parent_key, look, parent_map);
  for (const auto& [name, origins] : parent_map) {
    if (own_names.count(name)) continue;
    for (const auto& o : origins) out[name].insert(o);
  }
}

static void CollectEffectiveParamTypeNames(const ClassDecl* iface,
                                           const std::string& spec_key,
                                           const ClassLookup& look,
                                           NameOriginMap& out) {
  std::unordered_set<std::string_view> own_names;
  CollectOwnParamTypeNames(iface, own_names);
  for (auto n : own_names) out[n].insert(spec_key);
  ForEachInterfaceParent(iface, look,
                         [&](const ClassDecl* parent, std::string_view name,
                             const std::vector<DataType>& args) {
                           MergeInheritedParamTypeNames(
                               parent, MakeSpecKey(name, args, look.params),
                               look, own_names, out);
                         });
}

static void ValidateParamTypeConflicts(const ClassDecl* cls,
                                       const ClassLookup& look,
                                       DiagEngine& diag) {
  if (!cls->is_interface) return;
  std::unordered_set<std::string_view> own_names;
  CollectOwnParamTypeNames(cls, own_names);
  NameOriginMap inherited;
  ForEachInterfaceParent(cls, look,
                         [&](const ClassDecl* parent, std::string_view name,
                             const std::vector<DataType>& args) {
                           MergeInheritedParamTypeNames(
                               parent, MakeSpecKey(name, args, look.params),
                               look, own_names, inherited);
                         });
  for (const auto& [name, origins] : inherited) {
    if (origins.size() > 1) {
      diag.Error(
          cls->range.start,
          std::format("parameter or type '{}' in interface class '{}' is "
                      "inherited from multiple interface classes and must be "
                      "overridden",
                      name, cls->name),
          ConflictSubclause(
              std::vector<std::string_view>(origins.begin(), origins.end()),
              Subclause("8.26.6.2")));
    }
  }
}

static void CollectInterfaceTypedefNames(
    const ClassDecl* iface, const ClassLookup& look,
    std::unordered_set<std::string_view>& out,
    std::unordered_set<const ClassDecl*>& visited) {
  if (!visited.insert(iface).second) return;
  for (const auto* m : iface->members) {
    if (m->kind == ClassMemberKind::kTypedef) out.insert(m->name);
  }
  ForEachInterfaceParent(iface, look,
                         [&](const ClassDecl* parent, std::string_view,
                             const std::vector<DataType>&) {
                           CollectInterfaceTypedefNames(parent, look, out,
                                                        visited);
                         });
}

static void CollectClassVisibleTypeNames(
    const ClassDecl* cls, const CompilationUnit* unit,
    std::unordered_set<std::string_view>& out) {
  for (const auto* walk = cls; walk; walk = FindBaseClass(walk, unit)) {
    for (const auto* m : walk->members) {
      if (m->kind == ClassMemberKind::kTypedef) out.insert(m->name);
    }
    for (auto n : walk->type_param_names) out.insert(n);
  }
}

static bool IsCompilationUnitTypeName(std::string_view name,
                                      const CompilationUnit* unit) {
  for (const auto* c : unit->classes) {
    if (c->name == name) return true;
  }
  for (const auto* it : unit->cu_items) {
    if (it->kind == ModuleItemKind::kTypedef && it->name == name) return true;
  }
  return false;
}

static std::unordered_map<std::string_view, std::string_view>
CollectImplementedTypedefOwners(const ClassDecl* cls, const ClassLookup& look) {
  std::unordered_map<std::string_view, std::string_view> owning_iface;
  for (const auto& iref : cls->implements_types) {
    const auto* iface = FindReferencedClass(iref, look.unit);
    if (!iface || !iface->is_interface) continue;
    std::unordered_set<std::string_view> names;
    std::unordered_set<const ClassDecl*> visited;
    CollectInterfaceTypedefNames(iface, look, names, visited);
    for (auto n : names) owning_iface.emplace(n, iref.name);
  }
  return owning_iface;
}

void ElaboratorClassRules::ValidateImplementsTypeAccess(
    const ClassDecl* cls, const ScopeMap& params) {
  if (cls->is_interface || cls->implements_types.empty()) return;

  ClassLookup look{unit_, params};
  std::unordered_map<std::string_view, std::string_view> owning_iface =
      CollectImplementedTypedefOwners(cls, look);
  if (owning_iface.empty()) return;

  std::unordered_set<std::string_view> visible;
  CollectClassVisibleTypeNames(cls, unit_, visible);

  for (const auto* m : cls->members)
    CheckImplementsTypeAccessOfMember(m, owning_iface, visible);
}

void ElaboratorClassRules::CheckImplementsTypeAccessOfType(
    const DataType& dt, SourceLoc loc,
    const std::unordered_map<std::string_view, std::string_view>& owning_iface,
    const std::unordered_set<std::string_view>& visible) {
  if (dt.kind != DataTypeKind::kNamed || !dt.scope_name.empty()) return;
  auto owner = owning_iface.find(dt.type_name);
  if (owner == owning_iface.end()) return;
  if (visible.count(dt.type_name)) return;
  if (IsCompilationUnitTypeName(dt.type_name, unit_)) return;
  diag_.Error(
      loc,
      std::format("type '{}' is not inherited from interface class "
                  "'{}' through 'implements'; qualify it as '{}::{}'",
                  dt.type_name, owner->second, owner->second, dt.type_name),
      Subclause("8.26.3"));
}

void ElaboratorClassRules::CheckImplementsTypeAccessOfMember(
    const ClassMember* m,
    const std::unordered_map<std::string_view, std::string_view>& owning_iface,
    const std::unordered_set<std::string_view>& visible) {
  if (m->kind == ClassMemberKind::kProperty && !m->is_param) {
    CheckImplementsTypeAccessOfType(m->data_type, m->loc, owning_iface,
                                    visible);
    return;
  }
  if (m->kind != ClassMemberKind::kMethod || m->method == nullptr) return;
  CheckImplementsTypeAccessOfType(m->method->return_type, m->loc, owning_iface,
                                  visible);
  for (const auto& arg : m->method->func_args) {
    CheckImplementsTypeAccessOfType(arg.data_type, m->loc, owning_iface,
                                    visible);
  }
}

static void AppendWithNested(const ClassDecl* cls,
                             std::vector<const ClassDecl*>& out) {
  if (cls == nullptr) return;
  out.push_back(cls);
  for (const auto* m : cls->members) {
    if (m != nullptr && m->kind == ClassMemberKind::kClassDecl) {
      AppendWithNested(m->nested_class, out);
    }
  }
}

static std::vector<const ClassDecl*> ClassesAmong(
    const std::vector<ModuleItem*>& items) {
  std::vector<const ClassDecl*> out;
  for (const auto* item : items) {
    if (item != nullptr && item->kind == ModuleItemKind::kClassDecl) {
      AppendWithNested(item->class_decl, out);
    }
  }
  return out;
}

std::vector<ClassScope> DeclaredClassScopes(const CompilationUnit* unit) {
  std::vector<ClassScope> scopes;
  std::vector<const ClassDecl*> cu_classes;
  for (const auto* cls : unit->classes) AppendWithNested(cls, cu_classes);
  scopes.push_back({unit, &unit->cu_items, std::move(cu_classes)});
  for (const auto* group :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const auto* decl : *group) {
      scopes.push_back({unit, &decl->items, ClassesAmong(decl->items)});
    }
  }
  for (const auto* pkg : unit->packages) {
    scopes.push_back({unit, &pkg->items, ClassesAmong(pkg->items)});
  }
  return scopes;
}

static ScopeMap ScopeParamValues(const ClassScope& scope,
                                 const ScopeMap& cu_params) {
  ScopeMap values = cu_params;
  if (scope.items == nullptr) return values;
  for (const auto* item : *scope.items) {
    if (item == nullptr || item->kind != ModuleItemKind::kParamDecl) continue;
    if (item->init_expr == nullptr) continue;
    if (auto value = ConstEvalInt(item->init_expr, values))
      values[item->name] = *value;
  }
  return values;
}

struct OverrideNames {
  std::unordered_set<std::string_view> formals;
  std::unordered_set<std::string_view> non_integral;
};

static void ReportNonConstantSpecializationArgs(
    std::string_view base_name, const std::vector<DataType>& type_params,
    const ScopeMap& scope, const OverrideNames& names, DiagEngine& diag) {
  for (const auto& dt : type_params) {
    if (!dt.type_name.empty() || dt.type_ref_expr == nullptr) continue;
    const Expr* e = dt.type_ref_expr;
    if (IsConstantClassParamValue(e, scope)) continue;
    if (e->kind == ExprKind::kIdentifier && names.non_integral.count(e->text))
      continue;
    if (ExprMentionsAny(e, names.formals)) continue;
    diag.Error(dt.type_ref_expr->range.start,
               std::format("class '{}' parameter override is not a constant "
                           "expression",
                           base_name),
               Subclause("23.10.2"));
  }
}

static void ValidateSpecializationArgsInInheritance(const ClassDecl* cls,
                                                    const ClassScope& where,
                                                    const ScopeMap& scope,
                                                    DiagEngine& diag) {
  OverrideNames names{ClassParamNames(cls),
                      NonIntegralParamNames(where.items, scope)};
  ReportNonConstantSpecializationArgs(
      cls->base_class, cls->base_class_type_params, scope, names, diag);
  for (const auto& iref : cls->extends_interfaces)
    ReportNonConstantSpecializationArgs(iref.name, iref.type_params, scope,
                                        names, diag);
  for (const auto& iref : cls->implements_types)
    ReportNonConstantSpecializationArgs(iref.name, iref.type_params, scope,
                                        names, diag);
}

void ElaboratorClassRules::ValidateInterfaceClassRules() {
  for (const auto& scope : DeclaredClassScopes(unit_)) {
    ScopeMap params = ScopeParamValues(scope, cu_param_scope_);
    ClassLookup look{unit_, params};
    for (const auto* cls : scope.classes) {
      if (cls->is_interface) {
        ValidateInterfaceClassMembers(cls);
        ValidateInterfaceClassInheritance(cls, scope);
      } else {
        ValidateRegularClassInheritance(cls, scope);
        ValidateImplementsInterfaceMethods(cls);
        ValidateVirtualClassInterfaceObligations(cls, params);
        ValidateImplementsTypeAccess(cls, params);
      }

      ValidateMethodNameConflicts(cls, look, diag_);

      ValidateParamTypeConflicts(cls, look, diag_);

      ValidateSpecializationArgsInInheritance(cls, scope, params, diag_);
    }
  }
}

}  // namespace delta
