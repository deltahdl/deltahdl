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
               "virtual method override has different number of arguments",
               Clause::Unread());
    return;
  }
  for (size_t i = 0; i < base_args.size(); ++i) {
    if (!TypesMatch(base_args[i].data_type, over_args[i].data_type)) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument '{}' has "
                             "mismatched type",
                             over_args[i].name),
                 Clause::Unread());
    }
    if (base_args[i].name != over_args[i].name) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument name '{}' "
                             "does not match base '{}' ",
                             over_args[i].name, base_args[i].name),
                 Clause::Unread());
    }
    if (base_args[i].direction != over_args[i].direction) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument '{}' has "
                             "mismatched direction",
                             over_args[i].name),
                 Clause::Unread());
    }
    bool base_has_default = base_args[i].default_value != nullptr;
    bool over_has_default = over_args[i].default_value != nullptr;
    if (base_has_default != over_has_default) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument '{}': "
                             "presence of default must match",
                             over_args[i].name),
                 Clause::Unread());
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
               "virtual method override has mismatched return type",
               Clause::Unread());
  }
}

void Elaborator::ValidateOneMethodOverride(const ClassDecl* cls,
                                           const ClassMember* m) {
  auto* method = m->method;
  if (method->is_method_initial && method->is_method_extends) {
    diag_.Error(method->loc, "':initial' and ':extends' are mutually exclusive",
                Clause::Unread());
    return;
  }
  const auto* base_virtual = FindBaseVirtualMethod(cls, method->name, unit_);
  if (method->is_method_initial && base_virtual) {
    diag_.Error(method->loc,
                "method with ':initial' shall not override a virtual "
                "base class method",
                Clause::Unread());
  }
  if (method->is_method_extends && !base_virtual) {
    diag_.Error(method->loc,
                "method with ':extends' does not override a virtual "
                "base class method",
                Clause::Unread());
  }

  const auto* base_final = FindBaseFinalMethod(cls, method->name, unit_);
  if (base_final) {
    diag_.Error(method->loc, "cannot override a method declared ':final'",
                Clause::Unread());
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
                            cls->name, name),
                Clause::Unread());
  }
}

static void CheckPureFinalMember(const ClassMember* m, DiagEngine& diag) {
  if (m->kind == ClassMemberKind::kMethod && m->method) {
    if (m->is_pure_virtual && m->method->is_method_final) {
      diag.Error(m->method->loc,
                 "':final' shall not be specified on a pure virtual method",
                 Clause::Unread());
    }
  } else if (m->kind == ClassMemberKind::kConstraint) {
    if (m->is_pure_virtual && m->is_constraint_final) {
      diag.Error(m->loc, "':final' shall not be specified on a pure constraint",
                 Clause::Unread());
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
               "an interface class",
               Clause::Unread());
  }
  if (m->kind == ClassMemberKind::kMethod && !m->is_pure_virtual) {
    diag.Error(m->method ? m->method->loc : cls->range.start,
               std::format("interface class '{}' shall only contain "
                           "pure virtual methods",
                           cls->name),
               Clause::Unread());
  } else if (m->kind == ClassMemberKind::kProperty && !m->is_const &&
             !m->is_param) {
    // §8.26: an interface class may contain pure virtual methods, type
    // declarations, and parameter declarations; a parameter/localparam (carried
    // as kProperty with is_param) is not a data member.
    diag.Error(cls->range.start,
               std::format("interface class '{}' shall not contain "
                           "data members",
                           cls->name),
               Clause::Unread());
  } else if (m->kind == ClassMemberKind::kConstraint) {
    diag.Error(cls->range.start,
               std::format("interface class '{}' shall not contain "
                           "constraint blocks",
                           cls->name),
               Clause::Unread());
  } else if (m->kind == ClassMemberKind::kCovergroup) {
    diag.Error(cls->range.start,
               std::format("interface class '{}' shall not contain "
                           "covergroups",
                           cls->name),
               Clause::Unread());
  } else if (m->kind == ClassMemberKind::kClassDecl) {
    diag.Error(cls->range.start,
               std::format("interface class '{}' shall not contain "
                           "nested classes",
                           cls->name),
               Clause::Unread());
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
                             m->method->name, arg.name),
                 Clause::Unread());
    }
  }
}

void Elaborator::ValidateInterfaceClassMembers(const ClassDecl* cls) {
  // §8.26.8: a method-argument default is evaluated in the scope that contains
  // the subroutine declaration -- the interface class body. A value parameter
  // or local parameter of the class is a constant visible there by its bare
  // name, so layer the class's own parameters over the compilation-unit
  // parameter scope before checking defaults; otherwise a default naming such a
  // parameter would be wrongly rejected as non-constant.
  ScopeMap method_scope = cu_param_scope_;
  auto add_param = [&](std::string_view pname, const Expr* pexpr) {
    if (pname.empty() || method_scope.count(pname)) return;
    auto val = ConstEvalInt(pexpr, method_scope);
    method_scope[pname] = val.value_or(0);
  };
  for (const auto& [pname, pexpr] : cls->params) {
    if (cls->type_param_names.count(pname)) continue;
    add_param(pname, pexpr);
  }
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty && m->is_param)
      add_param(m->name, m->init_expr);
  }
  for (const auto* m : cls->members) {
    CheckInterfaceClassMemberKind(cls, m, diag_);
    CheckInterfaceClassMethodArgDefaults(m, method_scope, diag_);
  }
}

// §8.26.4's two questions are about the scope the class was written in rather
// than about the design: a forward typedef declared in one module says nothing
// about a class in another, and the order two declarations were written in only
// means anything among declarations that share a scope.
static bool IsForwardTypedefOnly(std::string_view name,
                                 const ClassDecl* before_cls,
                                 const ClassScope& scope) {
  bool has_forward = false;
  for (const auto* item : *scope.items) {
    if (item->kind == ModuleItemKind::kTypedef && item->name == name &&
        item->typedef_type.kind == DataTypeKind::kImplicit) {
      has_forward = true;
    }
  }
  if (!has_forward) return false;
  for (const auto* c : scope.classes) {
    if (c == before_cls) return true;
    if (c->name == name) return false;
  }
  return true;
}

static bool IsDeclaredBefore(std::string_view name, const ClassDecl* before_cls,
                             const ClassScope& scope) {
  for (const auto* c : scope.classes) {
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
                                    const ClassScope& scope, DiagEngine& diag,
                                    const InheritanceWording& wording) {
  if (cls->type_param_names.count(name) > 0) {
    diag.Error(cls->range.start,
               std::format("{} '{}' shall not {} type parameter '{}'",
                           wording.self_label, cls->name, wording.verb, name),
               Clause::Unread());
    return true;
  }
  if (IsForwardTypedefOnly(name, cls, scope)) {
    diag.Error(cls->range.start,
               std::format("{} '{}' shall not {} forward typedef '{}'; the "
                           "interface class must be declared before it is {}",
                           wording.self_label, cls->name, wording.verb, name,
                           wording.noun),
               Clause::Unread());
    return true;
  }
  if (!IsDeclaredBefore(name, cls, scope)) {
    const auto* target = FindClassDecl(name, scope.unit);
    if (target && target->is_interface) {
      diag.Error(cls->range.start,
                 std::format("interface class '{}' must be declared before it "
                             "is {} by '{}'",
                             name, wording.noun, cls->name),
                 Clause::Unread());
      return true;
    }
  }
  return false;
}

}  // namespace

void Elaborator::ValidateInterfaceClassInheritance(const ClassDecl* cls,
                                                   const ClassScope& scope) {
  if (!cls->implements_types.empty()) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' shall not use "
                            "'implements'",
                            cls->name),
                Clause::Unread());
  }
  if (cls->base_class.empty()) return;

  ValidateInheritedInterfaceName(cls, cls->base_class, scope, diag_,
                                 {"extend", "extended", "interface class"});
  const auto* base = FindClassDecl(cls->base_class, unit_);
  if (base && !base->is_interface) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' cannot extend "
                            "non-interface class '{}'",
                            cls->name, cls->base_class),
                Clause::Unread());
  }
  for (const auto& ref : cls->extends_interfaces) {
    auto iface_name = ref.name;
    if (ValidateInheritedInterfaceName(
            cls, iface_name, scope, diag_,
            {"extend", "extended", "interface class"})) {
      continue;
    }
    const auto* ibase = FindClassDecl(iface_name, unit_);
    if (ibase && !ibase->is_interface) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' cannot extend "
                              "non-interface class '{}'",
                              cls->name, iface_name),
                  Clause::Unread());
    }
  }
}

void Elaborator::ValidateRegularClassInheritance(const ClassDecl* cls,
                                                 const ClassScope& scope) {
  if (!cls->base_class.empty()) {
    const auto* base = FindClassDecl(cls->base_class, unit_);
    if (base && base->is_interface) {
      diag_.Error(cls->range.start,
                  std::format("class '{}' cannot extend interface class "
                              "'{}'; use 'implements' instead",
                              cls->name, cls->base_class),
                  Clause::Unread());
    }
  }
  for (const auto& ref : cls->implements_types) {
    auto impl_name = ref.name;
    if (ValidateInheritedInterfaceName(cls, impl_name, scope, diag_,
                                       {"implement", "implemented", "class"})) {
      continue;
    }
    const auto* impl = FindClassDecl(impl_name, unit_);
    if (impl && !impl->is_interface) {
      diag_.Error(cls->range.start,
                  std::format("class '{}' cannot implement non-interface "
                              "class '{}'",
                              cls->name, impl_name),
                  Clause::Unread());
    }
  }
}

}  // namespace delta
