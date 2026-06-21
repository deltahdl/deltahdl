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

// Walks the base-class chain of `cls` (excluding `cls` itself) and returns the
// first method named `method_name` for which `accept` holds, or nullptr.
static const ClassMember* FindBaseMethod(
    const ClassDecl* cls, std::string_view method_name,
    const CompilationUnit* unit,
    const std::function<bool(const ClassMember*)>& accept) {
  if (cls->base_class.empty()) return nullptr;
  for (const auto* c = FindClassDecl(cls->base_class, unit); c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kMethod && m->method &&
          m->method->name == method_name && accept(m)) {
        return m;
      }
    }
  }
  return nullptr;
}

static const ClassMember* FindBaseVirtualMethod(const ClassDecl* cls,
                                                std::string_view method_name,
                                                const CompilationUnit* unit) {
  return FindBaseMethod(cls, method_name, unit, [](const ClassMember* m) {
    return m->is_virtual || m->is_pure_virtual;
  });
}

static const ClassMember* FindBaseFinalMethod(const ClassDecl* cls,
                                              std::string_view method_name,
                                              const CompilationUnit* unit) {
  return FindBaseMethod(cls, method_name, unit, [](const ClassMember* m) {
    return m->method->is_method_final;
  });
}

static void ValidateOverrideSignature(const ModuleItem* base_method,
                                      const ModuleItem* override_method,
                                      const CompilationUnit* unit,
                                      DiagEngine& diag) {
  const auto& base_args = base_method->func_args;
  const auto& over_args = override_method->func_args;
  if (base_args.size() != over_args.size()) {
    diag.Error(override_method->loc,
               "virtual method override has different number of arguments");
    return;
  }
  for (size_t i = 0; i < base_args.size(); ++i) {
    if (!TypesMatch(base_args[i].data_type, over_args[i].data_type)) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument '{}' has "
                             "mismatched type",
                             over_args[i].name));
    }
    if (base_args[i].name != over_args[i].name) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument name '{}' "
                             "does not match base '{}' ",
                             over_args[i].name, base_args[i].name));
    }
    if (base_args[i].direction != over_args[i].direction) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument '{}' has "
                             "mismatched direction",
                             over_args[i].name));
    }
    bool base_has_default = base_args[i].default_value != nullptr;
    bool over_has_default = over_args[i].default_value != nullptr;
    if (base_has_default != over_has_default) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument '{}': "
                             "presence of default must match",
                             over_args[i].name));
    }
  }
  if (!TypesMatch(base_method->return_type, override_method->return_type)) {
    if (base_method->return_type.kind == DataTypeKind::kNamed &&
        override_method->return_type.kind == DataTypeKind::kNamed &&
        IsClassDerivedFrom(override_method->return_type.type_name,
                           base_method->return_type.type_name, unit)) {
      return;
    }
    diag.Error(override_method->loc,
               "virtual method override has mismatched return type");
  }
}

void Elaborator::ValidateOneMethodOverride(const ClassDecl* cls,
                                           const ClassMember* m) {
  auto* method = m->method;
  if (method->is_method_initial && method->is_method_extends) {
    diag_.Error(method->loc,
                "':initial' and ':extends' are mutually exclusive");
    return;
  }
  const auto* base_virtual = FindBaseVirtualMethod(cls, method->name, unit_);
  if (method->is_method_initial && base_virtual) {
    diag_.Error(method->loc,
                "method with ':initial' shall not override a virtual "
                "base class method");
  }
  if (method->is_method_extends && !base_virtual) {
    diag_.Error(method->loc,
                "method with ':extends' does not override a virtual "
                "base class method");
  }

  const auto* base_final = FindBaseFinalMethod(cls, method->name, unit_);
  if (base_final) {
    diag_.Error(method->loc, "cannot override a method declared ':final'");
  }

  if (base_virtual && base_virtual->method) {
    ValidateOverrideSignature(base_virtual->method, method, unit_, diag_);
  }
}

void Elaborator::ValidateVirtualMethodOverrides() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      ValidateOneMethodOverride(cls, m);
    }
  }
}

static void CollectPureVirtualMethods(
    const ClassDecl* cls, const CompilationUnit* unit,
    std::vector<std::string_view>& pure_names) {
  if (!cls) return;
  if (!cls->base_class.empty()) {
    const auto* base = FindClassDecl(cls->base_class, unit);
    CollectPureVirtualMethods(base, unit, pure_names);
  }
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
    if (m->is_pure_virtual) {
      pure_names.push_back(m->method->name);
    } else if (m->is_virtual) {
      std::erase(pure_names, m->method->name);
    }
  }
}

void Elaborator::ValidateAbstractClassUnimplemented(const ClassDecl* cls) {
  // §8.26: an interface class inherits pure virtual methods from the interfaces
  // it extends; it does not implement them. Only a non-virtual, non-interface
  // class is required to provide implementations.
  if (cls->is_virtual || cls->is_interface || cls->base_class.empty()) return;
  std::vector<std::string_view> unimpl;
  CollectPureVirtualMethods(cls, unit_, unimpl);
  for (auto name : unimpl) {
    diag_.Error(cls->range.start,
                std::format("non-abstract class '{}' does not implement "
                            "pure virtual method '{}'",
                            cls->name, name));
  }
}

static void CheckPureFinalMember(const ClassMember* m, DiagEngine& diag) {
  if (m->kind == ClassMemberKind::kMethod && m->method) {
    if (m->is_pure_virtual && m->method->is_method_final) {
      diag.Error(m->method->loc,
                 "':final' shall not be specified on a pure virtual method");
    }
  } else if (m->kind == ClassMemberKind::kConstraint) {
    if (m->is_pure_virtual && m->is_constraint_final) {
      diag.Error(m->loc,
                 "':final' shall not be specified on a pure constraint");
    }
  }
}

void Elaborator::ValidateAbstractClassRules() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      CheckPureFinalMember(m, diag_);
    }
    ValidateAbstractClassUnimplemented(cls);
  }
}

// Checks the kind/legality of a single interface-class member, mirroring the
// original dispatch chain (override specifiers + the disallowed member kinds).
static void CheckInterfaceClassMemberKind(const ClassDecl* cls,
                                          const ClassMember* m,
                                          DiagEngine& diag) {
  if (m->kind == ClassMemberKind::kMethod && m->method &&
      (m->method->is_method_initial || m->method->is_method_extends ||
       m->method->is_method_final)) {
    diag.Error(m->method->loc,
               "dynamic_override_specifiers shall not be used in "
               "an interface class");
  }
  if (m->kind == ClassMemberKind::kMethod && !m->is_pure_virtual) {
    diag.Error(m->method ? m->method->loc : cls->range.start,
               std::format("interface class '{}' shall only contain "
                           "pure virtual methods",
                           cls->name));
  } else if (m->kind == ClassMemberKind::kProperty && !m->is_const &&
             !m->is_param) {
    // §8.26: an interface class may contain pure virtual methods, type
    // declarations, and parameter declarations; a parameter/localparam (carried
    // as kProperty with is_param) is not a data member.
    diag.Error(cls->range.start,
               std::format("interface class '{}' shall not contain "
                           "data members",
                           cls->name));
  } else if (m->kind == ClassMemberKind::kConstraint) {
    diag.Error(cls->range.start,
               std::format("interface class '{}' shall not contain "
                           "constraint blocks",
                           cls->name));
  } else if (m->kind == ClassMemberKind::kCovergroup) {
    diag.Error(cls->range.start,
               std::format("interface class '{}' shall not contain "
                           "covergroups",
                           cls->name));
  } else if (m->kind == ClassMemberKind::kClassDecl) {
    diag.Error(cls->range.start,
               std::format("interface class '{}' shall not contain "
                           "nested classes",
                           cls->name));
  }
}

// Verifies that any default argument values on an interface-class method are
// constant expressions.
static void CheckInterfaceClassMethodArgDefaults(const ClassMember* m,
                                                 const ScopeMap& param_scope,
                                                 DiagEngine& diag) {
  if (m->kind != ClassMemberKind::kMethod || !m->method) return;
  for (const auto& arg : m->method->func_args) {
    if (arg.default_value && !IsConstantExpr(arg.default_value, param_scope)) {
      diag.Error(m->method->loc,
                 std::format("interface class method '{}' argument '{}': "
                             "default value must be a constant expression",
                             m->method->name, arg.name));
    }
  }
}

void Elaborator::ValidateInterfaceClassMembers(const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    CheckInterfaceClassMemberKind(cls, m, diag_);
    CheckInterfaceClassMethodArgDefaults(m, cu_param_scope_, diag_);
  }
}

static bool IsForwardTypedefOnly(std::string_view name,
                                 const ClassDecl* before_cls,
                                 const CompilationUnit* unit) {
  bool has_forward = false;
  for (const auto* item : unit->cu_items) {
    if (item->kind == ModuleItemKind::kTypedef && item->name == name &&
        item->typedef_type.kind == DataTypeKind::kImplicit) {
      has_forward = true;
    }
  }
  if (!has_forward) return false;
  for (const auto* c : unit->classes) {
    if (c == before_cls) return true;
    if (c->name == name) return false;
  }
  return true;
}

static bool IsDeclaredBefore(std::string_view name, const ClassDecl* before_cls,
                             const CompilationUnit* unit) {
  for (const auto* c : unit->classes) {
    if (c == before_cls) return false;
    if (c->name == name) return true;
  }
  return false;
}

namespace {

// §8.26: how one interface-inheritance relationship is phrased in diagnostics
// (verb/noun = extend/extended or implement/implemented; self_label names the
// owning class). The three move together as one relationship.
struct InheritanceWording {
  std::string_view verb, noun, self_label;
};
// Shared per-name validation for a base/extended/implemented interface name.
// Returns true when a diagnostic was emitted that should stop further checks on
// this name (mirrors the original `continue`/early-out control flow).
bool ValidateInheritedInterfaceName(const ClassDecl* cls, std::string_view name,
                                    const CompilationUnit* unit,
                                    DiagEngine& diag,
                                    const InheritanceWording& wording) {
  if (cls->type_param_names.count(name) > 0) {
    diag.Error(cls->range.start,
               std::format("{} '{}' shall not {} type parameter '{}'",
                           wording.self_label, cls->name, wording.verb, name));
    return true;
  }
  if (IsForwardTypedefOnly(name, cls, unit)) {
    diag.Error(cls->range.start,
               std::format("{} '{}' shall not {} forward typedef '{}'; the "
                           "interface class must be declared before it is {}",
                           wording.self_label, cls->name, wording.verb, name,
                           wording.noun));
    return true;
  }
  if (!IsDeclaredBefore(name, cls, unit)) {
    const auto* target = FindClassDecl(name, unit);
    if (target && target->is_interface) {
      diag.Error(cls->range.start,
                 std::format("interface class '{}' must be declared before it "
                             "is {} by '{}'",
                             name, wording.noun, cls->name));
      return true;
    }
  }
  return false;
}

}  // namespace

void Elaborator::ValidateInterfaceClassInheritance(const ClassDecl* cls) {
  if (!cls->implements_types.empty()) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' shall not use "
                            "'implements'",
                            cls->name));
  }
  if (cls->base_class.empty()) return;

  ValidateInheritedInterfaceName(cls, cls->base_class, unit_, diag_,
                                 {"extend", "extended", "interface class"});
  const auto* base = FindClassDecl(cls->base_class, unit_);
  if (base && !base->is_interface) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' cannot extend "
                            "non-interface class '{}'",
                            cls->name, cls->base_class));
  }
  for (const auto& ref : cls->extends_interfaces) {
    auto iface_name = ref.name;
    if (ValidateInheritedInterfaceName(
            cls, iface_name, unit_, diag_,
            {"extend", "extended", "interface class"})) {
      continue;
    }
    const auto* ibase = FindClassDecl(iface_name, unit_);
    if (ibase && !ibase->is_interface) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' cannot extend "
                              "non-interface class '{}'",
                              cls->name, iface_name));
    }
  }
}

void Elaborator::ValidateRegularClassInheritance(const ClassDecl* cls) {
  if (!cls->base_class.empty()) {
    const auto* base = FindClassDecl(cls->base_class, unit_);
    if (base && base->is_interface) {
      diag_.Error(cls->range.start,
                  std::format("class '{}' cannot extend interface class "
                              "'{}'; use 'implements' instead",
                              cls->name, cls->base_class));
    }
  }
  for (const auto& ref : cls->implements_types) {
    auto impl_name = ref.name;
    if (ValidateInheritedInterfaceName(cls, impl_name, unit_, diag_,
                                       {"implement", "implemented", "class"})) {
      continue;
    }
    const auto* impl = FindClassDecl(impl_name, unit_);
    if (impl && !impl->is_interface) {
      diag_.Error(cls->range.start,
                  std::format("class '{}' cannot implement non-interface "
                              "class '{}'",
                              cls->name, impl_name));
    }
  }
}

static bool MethodSignaturesCompatible(const ModuleItem* a,
                                       const ModuleItem* b) {
  if (!TypesMatch(a->return_type, b->return_type)) return false;
  if (a->func_args.size() != b->func_args.size()) return false;
  for (size_t i = 0; i < a->func_args.size(); ++i) {
    if (!TypesMatch(a->func_args[i].data_type, b->func_args[i].data_type))
      return false;
    if (a->func_args[i].direction != b->func_args[i].direction) return false;
  }
  return true;
}

static std::string MakeSpecKey(std::string_view name,
                               const std::vector<DataType>& type_params) {
  if (type_params.empty()) return std::string(name);
  std::string key(name);
  key += "#(";
  for (size_t i = 0; i < type_params.size(); ++i) {
    if (i > 0) key += ',';
    const auto& dt = type_params[i];
    if (!dt.type_name.empty())
      key += dt.type_name;
    else
      key += std::to_string(static_cast<int>(dt.kind));
  }
  key += ')';
  return key;
}

using IfaceMethodMap =
    std::unordered_map<std::string_view,
                       std::vector<std::pair<std::string, const ModuleItem*>>>;

static void ForEachInterfaceParent(
    const ClassDecl* cls, const CompilationUnit* unit,
    const std::function<void(const ClassDecl*, const std::string&)>& fn);

static void CollectInterfacePureVirtualMethods(
    const ClassDecl* iface, const std::string& spec_key,
    const CompilationUnit* unit, IfaceMethodMap& out,
    std::unordered_set<std::string>& visited) {
  if (!visited.insert(spec_key).second) return;
  for (const auto* m : iface->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->is_pure_virtual) continue;
    if (!m->method) continue;
    out[m->method->name].push_back({spec_key, m->method});
  }
  ForEachInterfaceParent(
      iface, unit, [&](const ClassDecl* parent, const std::string& key) {
        CollectInterfacePureVirtualMethods(parent, key, unit, out, visited);
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
                                           const CompilationUnit* unit,
                                           IfaceMethodMap& iface_methods) {
  std::unordered_set<std::string> visited;
  if (cls->is_interface) {
    ForEachInterfaceParent(
        cls, unit, [&](const ClassDecl* parent, const std::string& key) {
          CollectInterfacePureVirtualMethods(parent, key, unit, iface_methods,
                                             visited);
        });
  } else {
    std::vector<InterfaceRef> all_ifaces;
    CollectImplementedInterfaces(cls, unit, all_ifaces);
    std::unordered_set<std::string> seen_iface;
    for (const auto& iref : all_ifaces) {
      auto iface_key = MakeSpecKey(iref.name, iref.type_params);
      if (!seen_iface.insert(iface_key).second) continue;
      const auto* iface = FindClassDecl(iref.name, unit);
      if (!iface || !iface->is_interface) continue;
      CollectInterfacePureVirtualMethods(iface, iface_key, unit, iface_methods,
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
      if (!MethodSignaturesCompatible(first_method, entries[i].second)) {
        diag.Error(
            cls->range.start,
            std::format("method name conflict for '{}' in '{}': incompatible "
                        "signatures in interface '{}' and interface '{}'",
                        method_name, cls->name, entries[0].first,
                        entries[i].first));
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
    for (const auto& [iface_name, iface_method] : entries) {
      if (!MethodSignaturesCompatible(impl, iface_method)) {
        diag.Error(impl->loc,
                   std::format("method '{}' does not match signature of pure "
                               "virtual method '{}' in interface '{}'",
                               method_name, method_name, iface_name));
        break;
      }
    }
  }
}

static void ValidateMethodNameConflicts(const ClassDecl* cls,
                                        const CompilationUnit* unit,
                                        DiagEngine& diag) {
  IfaceMethodMap iface_methods;
  CollectInScopeInterfaceMethods(cls, unit, iface_methods);
  DiagnoseInterfaceSignatureConflicts(cls, iface_methods, diag);
  if (!cls->is_interface) {
    DiagnoseImplSignatureMismatches(cls, iface_methods, unit, diag);
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
                             impl->name, impl_args[i].name, iface_name));
      continue;
    }
    if (!iface_has) continue;
    auto iface_val = ConstEvalInt(iface_args[i].default_value);
    auto impl_val = ConstEvalInt(impl_args[i].default_value);
    if (iface_val && impl_val && *iface_val != *impl_val) {
      diag.Error(impl->loc,
                 std::format("method '{}' argument '{}': default value "
                             "does not match interface '{}' (expected {}, "
                             "got {})",
                             impl->name, impl_args[i].name, iface_name,
                             *iface_val, *impl_val));
    }
  }
}

static void CheckInterfaceMethods(const ClassDecl* cls, const ClassDecl* iface,
                                  std::string_view iface_name,
                                  const CompilationUnit* unit,
                                  DiagEngine& diag) {
  for (const auto* im : iface->members) {
    if (im->kind != ClassMemberKind::kMethod || !im->is_pure_virtual) continue;
    if (!im->method) continue;
    const auto* impl =
        FindConcreteMethodInHierarchy(cls, im->method->name, unit);
    if (!impl) {
      diag.Error(cls->range.start,
                 std::format("class '{}' does not implement pure virtual "
                             "method '{}' from interface '{}'",
                             cls->name, im->method->name, iface_name));
      continue;
    }
    CheckImplInterfaceArgDefaults(im->method, impl, iface_name, diag);
  }
}

void Elaborator::ValidateImplementsInterfaceMethods(const ClassDecl* cls) {
  if (cls->is_virtual) return;
  std::vector<InterfaceRef> all_ifaces;
  CollectImplementedInterfaces(cls, unit_, all_ifaces);
  if (all_ifaces.empty()) return;
  std::unordered_set<std::string> seen;
  for (const auto& iref : all_ifaces) {
    auto iface_key = MakeSpecKey(iref.name, iref.type_params);
    if (!seen.insert(iface_key).second) continue;
    const auto* iface = FindClassDecl(iref.name, unit_);
    if (!iface) continue;
    CheckInterfaceMethods(cls, iface, iref.name, unit_, diag_);
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
    const ClassDecl* cls, const CompilationUnit* unit,
    const std::function<void(const ClassDecl*, const std::string&)>& fn) {
  if (!cls->base_class.empty()) {
    const auto* base = FindClassDecl(cls->base_class, unit);
    if (base && base->is_interface) {
      fn(base, MakeSpecKey(cls->base_class, cls->base_class_type_params));
    }
  }
  for (const auto& ref : cls->extends_interfaces) {
    const auto* ext = FindClassDecl(ref.name, unit);
    if (ext && ext->is_interface) {
      fn(ext, MakeSpecKey(ref.name, ref.type_params));
    }
  }
}

static void CollectEffectiveParamTypeNames(const ClassDecl* iface,
                                           const std::string& spec_key,
                                           const CompilationUnit* unit,
                                           NameOriginMap& out);

// Merges the effective param/type names of `parent` into `out`, skipping names
// already owned locally (recorded in `own_names`).
static void MergeInheritedParamTypeNames(
    const ClassDecl* parent, const std::string& parent_key,
    const CompilationUnit* unit,
    const std::unordered_set<std::string_view>& own_names, NameOriginMap& out) {
  NameOriginMap parent_map;
  CollectEffectiveParamTypeNames(parent, parent_key, unit, parent_map);
  for (const auto& [name, origins] : parent_map) {
    if (own_names.count(name)) continue;
    for (const auto& o : origins) out[name].insert(o);
  }
}

static void CollectEffectiveParamTypeNames(const ClassDecl* iface,
                                           const std::string& spec_key,
                                           const CompilationUnit* unit,
                                           NameOriginMap& out) {
  std::unordered_set<std::string_view> own_names;
  CollectOwnParamTypeNames(iface, own_names);
  for (auto n : own_names) out[n].insert(spec_key);
  ForEachInterfaceParent(
      iface, unit, [&](const ClassDecl* parent, const std::string& parent_key) {
        MergeInheritedParamTypeNames(parent, parent_key, unit, own_names, out);
      });
}

static void ValidateParamTypeConflicts(const ClassDecl* cls,
                                       const CompilationUnit* unit,
                                       DiagEngine& diag) {
  if (!cls->is_interface) return;
  std::unordered_set<std::string_view> own_names;
  CollectOwnParamTypeNames(cls, own_names);
  NameOriginMap inherited;
  ForEachInterfaceParent(
      cls, unit, [&](const ClassDecl* parent, const std::string& parent_key) {
        MergeInheritedParamTypeNames(parent, parent_key, unit, own_names,
                                     inherited);
      });
  for (const auto& [name, origins] : inherited) {
    if (origins.size() > 1) {
      diag.Error(
          cls->range.start,
          std::format("parameter or type '{}' in interface class '{}' is "
                      "inherited from multiple interface classes and must be "
                      "overridden",
                      name, cls->name));
    }
  }
}

void Elaborator::ValidateInterfaceClassRules() {
  for (const auto* cls : unit_->classes) {
    if (cls->is_interface) {
      ValidateInterfaceClassMembers(cls);
      ValidateInterfaceClassInheritance(cls);
    } else {
      ValidateRegularClassInheritance(cls);
      ValidateImplementsInterfaceMethods(cls);
    }

    ValidateMethodNameConflicts(cls, unit_, diag_);

    ValidateParamTypeConflicts(cls, unit_, diag_);
  }
}

}  // namespace delta
