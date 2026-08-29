#include <algorithm>
#include <format>
#include <functional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

// §8.25.1/§8.26: the binding a parameterized class's formal type parameters
// take in one specialization of it, keyed by the formal's name.
using TypeSubst = std::unordered_map<std::string_view, DataType>;

// Rewrites `type` under `subst`. A type written as a bare name is a formal type
// parameter when the specialization binds that name, in which case the type it
// was specialized with stands there instead; anything else is already a type
// and stands for itself. The result is returned by value: one of the two types
// it may name is the argument, and handing back a reference to that would
// outlive a caller that passed a temporary.
static DataType ResolveType(const DataType& type, const TypeSubst& subst) {
  if (type.type_name.empty()) return type;
  auto it = subst.find(type.type_name);
  return it == subst.end() ? type : it->second;
}

// True when the two methods agree on return type, argument count, argument
// types and argument directions, each side read under the specialization it was
// reached through. §8.26 requires an implementing method to match the prototype
// of the pure virtual method it implements, and for a parameterized interface
// class that prototype is the one its type arguments produce, not the one its
// formal parameters were written with.
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
      // A value parameter argument (e.g. `#(2)`) folds no type name and parses
      // as an implicit-typed slot carrying the value expression. §8.26.6.3
      // rules that "Each unique parameterization of a parameterized interface
      // class is an interface class specialization", and that different
      // specializations are not a diamond, so two different constant values
      // must yield different keys; otherwise a value-parameterized base reached
      // through two paths with different arguments would be mistaken for a
      // single diamond and its inherited names would wrongly collapse instead
      // of colliding.
      //
      // The fold is given the parameter scope of whatever declared the class,
      // so a named constant keys by its value: `I#(2)` and `I#(A)` with
      // `localparam int A = 2` are one specialization, which §8.26.6.3 requires
      // because uniqueness is of the parameterization and not of how it was
      // spelled. ScopeParamValues is what puts a parameter declared in a
      // module, an interface, a program or a checker into that scope, which the
      // compilation-unit scope alone does not hold: this validation runs from
      // Elaborator::RunPreElaborationClassValidations, before any of those is
      // elaborated.
      //
      // "v?" remains for the argument naming the class's own formal value
      // parameter, which has no value until the class is itself specialized.
      // Two parameterizations that share "v?" are read here as one
      // specialization, and that stays the safer of the two errors: splitting
      // them -- by source position, say -- would report a name collision
      // between a parameterization and itself. Every other unfoldable argument
      // is reported by ValidateSpecializationArgsInInheritance rather than
      // reaching this branch quietly.
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

// §8.26: one specialization of an interface class -- the name it is known by
// once its type arguments are written in, and the binding those arguments give
// its formal type parameters. Both are properties of the specialization rather
// than of the interface class, so they travel together.
struct IfaceSpec {
  std::string key;
  TypeSubst subst;
};

// What every step of an inheritance walk has to answer two questions with:
// where a class name is declared, and what a constant name is worth. §3.12
// makes the compilation unit what a class name is looked up in. §11.2.1 makes
// a specialization's value argument a constant expression and lists
// "parameters" among the operands one consists of, so keying a specialization
// by its argument needs the values those parameters were given. The two travel
// together because a parent is resolved and keyed at the same step.
struct ClassLookup {
  const CompilationUnit* unit;
  const ScopeMap& params;
};

using IfaceMethodMap =
    std::unordered_map<std::string_view,
                       std::vector<std::pair<IfaceSpec, const ModuleItem*>>>;

// The formal type parameters of `cls` in declaration order. The parameter list
// holds value and type parameters together in the order they were written, and
// `type_param_names` says which of them are types; a type argument in position
// i binds the i-th name this returns.
static std::vector<std::string_view> TypeParamNames(const ClassDecl* cls) {
  std::vector<std::string_view> names;
  for (const auto& [pname, _] : cls->params) {
    if (cls->type_param_names.count(pname) != 0) names.push_back(pname);
  }
  return names;
}

// Builds the specialization `iface` is reached as when named with `args` from a
// context whose own specialization is `outer`.
//
// An argument may itself be a formal type parameter of the naming context, as
// `TYPE` is in `interface class PutGetIntf#(type TYPE) extends PutImp#(TYPE)`.
// Resolving each argument through `outer` before binding it is what carries a
// type argument down a chain of extends clauses: specializing PutGetIntf with
// `int` binds TYPE to int, which makes the parent PutImp#(int) and binds its
// own formal T to int in turn.
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

// Calls `fn` once per interface class `cls` inherits from directly, with the
// type arguments it was named with.
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
    const auto* base = FindClassDecl(cls->base_class, unit);
    if (base && !base->is_interface) {
      CollectImplementedInterfaces(base, unit, out);
    }
  }
}

// Gathers the pure virtual methods contributed by every interface in scope for
// `cls`, keyed by method name, into `iface_methods`.
static void CollectInScopeInterfaceMethods(const ClassDecl* cls,
                                           const ClassLookup& look,
                                           IfaceMethodMap& iface_methods) {
  std::unordered_set<std::string> visited;
  // The class naming the interfaces binds no type parameters of its own into
  // them: an argument it writes is a type, or a formal of an enclosing
  // parameterization that is not in scope here.
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
      const auto* iface = FindClassDecl(iref.name, look.unit);
      if (!iface || !iface->is_interface) continue;
      auto spec =
          MakeIfaceSpec(iface, iref.name, iref.type_params, outer, look.params);
      if (!seen_iface.insert(spec.key).second) continue;
      CollectInterfacePureVirtualMethods(iface, spec, look, iface_methods,
                                         visited);
    }
  }
}

// Reports two interfaces in scope contributing the same method name with
// incompatible signatures.
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
            Subclause("8.26.6.1"));
        break;
      }
    }
  }
}

// Walks the base-class chain of `cls` (excluding `cls`) and returns the first
// virtual method named `method_name`. When `require_non_pure` is set, pure
// virtual methods are skipped.
static const ModuleItem* FindVirtualMethodInBaseChain(
    const ClassDecl* cls, std::string_view method_name,
    const CompilationUnit* unit, bool require_non_pure) {
  for (const auto* walk = cls->base_class.empty()
                              ? nullptr
                              : FindClassDecl(cls->base_class, unit);
       walk; walk = walk->base_class.empty()
                        ? nullptr
                        : FindClassDecl(walk->base_class, unit)) {
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

// Locates the concrete (virtual) implementation of `method_name` for `cls`,
// searching the class itself first and then walking the base-class chain.
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
  return FindVirtualMethodInBaseChain(cls, method_name, unit,
                                      /*require_non_pure=*/false);
}

// Checks that each implementing method matches the signature of every interface
// pure virtual method of the same name.
static void DiagnoseImplSignatureMismatches(const ClassDecl* cls,
                                            const IfaceMethodMap& iface_methods,
                                            const CompilationUnit* unit,
                                            DiagEngine& diag) {
  for (const auto& [method_name, entries] : iface_methods) {
    const ModuleItem* impl = FindMethodNameConflictImpl(cls, method_name, unit);
    if (!impl) continue;
    // The implementing method is written in the implementing class, whose own
    // names are already types; only the interface side carries a binding.
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
  return FindVirtualMethodInBaseChain(cls, method_name, unit,
                                      /*require_non_pure=*/true);
}

// §8.26.8: an implementing method's argument defaults must mirror the interface
// prototype's (matching presence and, where both present, the same value).
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
    // Fold each default against the compilation-unit parameter scope so a
    // named-constant default (a parameter or localparam per 11.2.1), not just a
    // bare literal, is compared by value for the "same for all implementors"
    // rule.
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

// §8.26: an interface class an implementing class is checked against -- its
// declaration and the name the `implements` clause reached it by.
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
    const auto* iface = FindClassDecl(iref.name, unit_);
    // §8.26 poses the obligation to implement a pure virtual method only for an
    // interface class: "the Fifo class is also implementing the PutImp and
    // GetImp interface classes so it shall provide implementations for the put
    // and get methods" (printed page 209 of ~/LRM.pdf). A name that resolves to
    // anything else is already rejected under §8.26.2 by
    // ValidateRegularClassInheritance in
    // src/elaborator/elaborator_validate_class_overrides.cpp, so reporting it
    // here as well would call a virtual class an interface class.
    if (!iface || !iface->is_interface) continue;
    CheckInterfaceMethods(cls, {iface, iref.name}, unit_, cu_param_scope_,
                          diag_);
  }
}

// §8.26.7: returns true when virtual class `cls`, or a class in its base chain,
// carries a method named `method_name` that is either a virtual implementation
// or a re-declared pure virtual prototype — the two ways a virtual class may
// discharge (or forward) an interface-class prototype obligation.
static bool VirtualClassAddressesPrototype(const ClassDecl* cls,
                                           std::string_view method_name,
                                           const CompilationUnit* unit) {
  for (const auto* walk = cls; walk;
       walk = walk->base_class.empty()
                  ? nullptr
                  : FindClassDecl(walk->base_class, unit)) {
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

// §8.26.7: a virtual class may take advantage of an interface class through a
// partial implementation, but for each interface-class method prototype it must
// either supply a virtual method implementation or re-declare the prototype
// with the `pure` qualifier. Leaving a prototype neither implemented nor
// re-declared is illegal. Only the interfaces named directly in this virtual
// class's `implements` clause create the obligation here; a prototype inherited
// through a base class is the implementing base's responsibility.
void ElaboratorClassRules::ValidateVirtualClassInterfaceObligations(
    const ClassDecl* cls, const ScopeMap& params) {
  if (!cls->is_virtual || cls->is_interface || cls->implements_types.empty())
    return;
  std::unordered_set<std::string> seen_iface;
  TypeSubst outer;
  ClassLookup look{unit_, params};
  for (const auto& iref : cls->implements_types) {
    const auto* iface = FindClassDecl(iref.name, unit_);
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

// Invokes `fn(parent, parent_key)` for every interface parent of `cls`: the
// base class (if it is an interface) followed by each extends-interface that is
// an interface. The spec key encodes the parent's type parameters.
static void ForEachInterfaceParent(
    const ClassDecl* cls, const ClassLookup& look,
    const std::function<void(const ClassDecl*, std::string_view,
                             const std::vector<DataType>&)>& fn) {
  if (!cls->base_class.empty()) {
    const auto* base = FindClassDecl(cls->base_class, look.unit);
    if (base && base->is_interface) {
      fn(base, cls->base_class, cls->base_class_type_params);
    }
  }
  for (const auto& ref : cls->extends_interfaces) {
    const auto* ext = FindClassDecl(ref.name, look.unit);
    if (ext && ext->is_interface) {
      fn(ext, ref.name, ref.type_params);
    }
  }
}

static void CollectEffectiveParamTypeNames(const ClassDecl* iface,
                                           const std::string& spec_key,
                                           const ClassLookup& look,
                                           NameOriginMap& out);

// Merges the effective param/type names of `parent` into `out`, skipping names
// already owned locally (recorded in `own_names`).
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
          Subclause("8.26.6.2"));
    }
  }
}

// Collects the names of typedef members declared by `iface` and, transitively,
// by every interface it extends. These are the names an implementing class can
// reach only through the class scope resolution operator on the interface
// (§8.26.3).
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

// Collects the type names visible unqualified inside `cls`: its own typedef
// members and type parameters plus those of every class in its base-class
// chain. §8.26.3 leaves exactly these (together with compilation-unit types)
// resolvable without a scope prefix; typedefs reached through `implements` are
// not among them.
static void CollectClassVisibleTypeNames(
    const ClassDecl* cls, const CompilationUnit* unit,
    std::unordered_set<std::string_view>& out) {
  for (const auto* walk = cls; walk;
       walk = walk->base_class.empty()
                  ? nullptr
                  : FindClassDecl(walk->base_class, unit)) {
    for (const auto* m : walk->members) {
      if (m->kind == ClassMemberKind::kTypedef) out.insert(m->name);
    }
    for (auto n : walk->type_param_names) out.insert(n);
  }
}

// True when `name` denotes a type declared at compilation-unit scope (a
// top-level class or typedef). Such a name resolves on its own, so its
// unqualified use in an implementing class is not the §8.26.3 error.
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

// §8.26.3: the parameters and typedefs of an interface class are not inherited
// by a class that implements it; they stay reachable only through the class
// scope resolution operator. A data member of the implementing class whose type
// is an unqualified name that would resolve only to such an interface typedef
// is therefore illegal — the name must be qualified with the interface.
// §8.26.5: every type name the interface classes of an `implements` clause
// declare, mapped to the interface the class reaches it through. The first
// interface to supply a name owns it.
static std::unordered_map<std::string_view, std::string_view>
CollectImplementedTypedefOwners(const ClassDecl* cls, const ClassLookup& look) {
  std::unordered_map<std::string_view, std::string_view> owning_iface;
  for (const auto& iref : cls->implements_types) {
    const auto* iface = FindClassDecl(iref.name, look.unit);
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

// §8.26.5: a type name an interface class declares is reachable unqualified
// only where `implements` inherits it. Report a use of one of those names that
// is not otherwise visible in the class or the compilation unit.
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

// The types a member writes down: a data property's own type, or the return
// type and argument types of a method. §8.26.3 governs each of them alike —
// the name a method spells for its return or for one of its arguments is
// resolved in the implementing class exactly as the name a data member spells.
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

// §8.1 lets a class declaration stand wherever a data declaration may, so a
// class may itself declare classes. Appends `cls` and then, after it, every
// class declared within it, leaving an enclosing class ahead of the ones it
// encloses and otherwise keeping the order they were written in.
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

// The classes `items` declares, in the order they were written, each followed
// by the classes it encloses.
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

// The values a specialization argument written in `scope` can name. These
// validations run before any module, interface, program or checker is
// elaborated, so a parameter declared in one has no value anywhere the
// compilation-unit scope reaches and has to be folded here from the items
// themselves. §6.20.1 lets a parameter's value depend on one declared before
// it, so the items are folded in the order they were written and each result is
// layered under its own name for the ones that follow.
//
// The compilation-unit scope is the base because §8.26.6.3 puts no restriction
// on where a specialization argument's value comes from, so one written inside
// a module may still name a compilation-unit or package constant. Re-folding
// the compilation-unit scope's own items over it costs a repeat of what
// RegisterCuScopeItems already computed and reaches the same values.
//
// A parameter whose value does not fold is absent, which leaves an argument
// naming it exactly as unfoldable as it was.
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

// §8.25 rules that instances of a parameterized class are instantiated "using
// the same parameter override rules (see 23.10)" (printed page 203 of IEEE
// 1800-2023), and §23.10.2 gives a parameter override a constant expression as
// its value. Reports a value argument of an extends or implements clause that
// is not one, with the message and subclause
// Elaborator::ValidateSpecializationArgsConstant already gives the same rule
// for the declaration form, so one rule reads one way wherever it is broken.
//
// An argument mentioning one of `cls`'s own parameter names is left alone. Such
// a value is computable only once `cls` is itself specialized, so it is not a
// constant expression that failed to fold, and Elaborator::RecordClassParam
// draws the same distinction with the same test for a class parameter's own
// initializer.
static void ReportNonConstantSpecializationArgs(
    std::string_view base_name, const std::vector<DataType>& type_params,
    const ScopeMap& scope, const std::unordered_set<std::string_view>& formals,
    DiagEngine& diag) {
  for (const auto& dt : type_params) {
    if (!dt.type_name.empty() || dt.type_ref_expr == nullptr) continue;
    if (ConstEvalInt(dt.type_ref_expr, scope)) continue;
    if (ExprMentionsAny(dt.type_ref_expr, formals)) continue;
    diag.Error(dt.type_ref_expr->range.start,
               std::format("class '{}' parameter override is not a constant "
                           "expression",
                           base_name),
               Subclause("23.10.2"));
  }
}

static void ValidateSpecializationArgsInInheritance(const ClassDecl* cls,
                                                    const ScopeMap& scope,
                                                    DiagEngine& diag) {
  auto formals = ClassParamNames(cls);
  ReportNonConstantSpecializationArgs(
      cls->base_class, cls->base_class_type_params, scope, formals, diag);
  for (const auto& iref : cls->extends_interfaces)
    ReportNonConstantSpecializationArgs(iref.name, iref.type_params, scope,
                                        formals, diag);
  for (const auto& iref : cls->implements_types)
    ReportNonConstantSpecializationArgs(iref.name, iref.type_params, scope,
                                        formals, diag);
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

      ValidateSpecializationArgsInInheritance(cls, params, diag_);
    }
  }
}

}  // namespace delta
