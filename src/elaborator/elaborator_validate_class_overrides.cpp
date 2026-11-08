#include <algorithm>
#include <cstddef>
#include <format>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/class_member_names.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct OwnedMethod {
  const ClassMember* member = nullptr;
  const ClassDecl* owner = nullptr;
};

struct OverrideTypeContext {
  const ClassDecl* base;
  const ClassDecl* derived;
  const TypedefMap& typedefs;
  const CompilationUnit* unit;
  const std::unordered_map<std::string_view, DataType>* bound = nullptr;
};

}  // namespace

static OwnedMethod FindBaseMethod(
    const ClassDecl* cls, std::string_view method_name,
    const CompilationUnit* unit,
    const std::function<bool(const ClassMember*)>& accept) {
  if (cls->base_class.empty()) return {};
  for (const auto* c = FindBaseClass(cls, unit); c;
       c = FindBaseClass(c, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kMethod && m->method &&
          m->method->name == method_name && accept(m)) {
        return {m, c};
      }
    }
  }
  return {};
}

static OwnedMethod FindBaseVirtualMethod(const ClassDecl* cls,
                                         std::string_view method_name,
                                         const CompilationUnit* unit) {
  return FindBaseMethod(cls, method_name, unit, [](const ClassMember* m) {
    return m->is_virtual || m->is_pure_virtual;
  });
}

static const ClassMember* FindBaseFinalMethod(const ClassDecl* cls,
                                              std::string_view method_name,
                                              const CompilationUnit* unit) {
  return FindBaseMethod(
             cls, method_name, unit,
             [](const ClassMember* m) { return m->method->is_method_final; })
      .member;
}

static DataType ResolvedType(const DataType& type, const ClassDecl& cls,
                             const TypedefMap& typedefs) {
  DataType resolved = type;
  if (resolved.kind == DataTypeKind::kNamed && resolved.scope_name.empty()) {
    for (const ClassMember* m : cls.members) {
      if (m->typedef_item != nullptr && m->name == resolved.type_name) {
        resolved = m->typedef_item->typedef_type;
      }
    }
  }
  if (const DataType* bound = FindNamedType(resolved, typedefs)) {
    resolved = *bound;
  }
  return resolved;
}

static bool NamesTypeParameter(const DataType& type, const ClassDecl& cls) {
  return type.kind == DataTypeKind::kNamed && type.scope_name.empty() &&
         cls.type_param_names.contains(type.type_name);
}

static bool OverrideTypeMismatch(const DataType& base, const DataType& over,
                                 bool is_return,
                                 const OverrideTypeContext& ctx) {
  DataType over_type = over;
  if (NamesTypeParameter(over, *ctx.derived)) {
    if (ctx.bound == nullptr) return false;
    over_type = ctx.bound->at(over.type_name);
  }
  if (NamesTypeParameter(base, *ctx.base)) return false;
  const DataType kBase = ResolvedType(base, *ctx.base, ctx.typedefs);
  const DataType kOver = ResolvedType(over_type, *ctx.derived, ctx.typedefs);
  if (TypesMatch(kBase, kOver)) return false;
  return !is_return || kBase.kind != DataTypeKind::kNamed ||
         kOver.kind != DataTypeKind::kNamed ||
         !IsClassDerivedFrom(kOver.type_name, kBase.type_name, ctx.unit);
}

static void ValidateOverrideSignature(const ModuleItem* base_method,
                                      const ModuleItem* override_method,
                                      const OverrideTypeContext& ctx,
                                      DiagEngine& diag) {
  const auto& base_args = base_method->func_args;
  const auto& over_args = override_method->func_args;
  if (base_args.size() != over_args.size()) {
    diag.Error(override_method->loc,
               "virtual method override has different number of arguments",
               Subclause("8.20"));
    return;
  }
  for (size_t i = 0; i < base_args.size(); ++i) {
    if (OverrideTypeMismatch(base_args[i].data_type, over_args[i].data_type,
                             false, ctx)) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument '{}' has "
                             "mismatched type",
                             over_args[i].name),
                 Subclause("8.20"));
    }
    if (base_args[i].name != over_args[i].name) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument name '{}' "
                             "does not match base '{}' ",
                             over_args[i].name, base_args[i].name),
                 Subclause("8.20"));
    }
    if (base_args[i].direction != over_args[i].direction) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument '{}' has "
                             "mismatched direction",
                             over_args[i].name),
                 Subclause("8.20"));
    }
    bool base_has_default = base_args[i].default_value != nullptr;
    bool over_has_default = over_args[i].default_value != nullptr;
    if (base_has_default != over_has_default) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument '{}': "
                             "presence of default must match",
                             over_args[i].name),
                 Subclause("8.20"));
    }
  }
  if (OverrideTypeMismatch(base_method->return_type,
                           override_method->return_type, true, ctx)) {
    diag.Error(override_method->loc,
               "virtual method override has mismatched return type",
               Subclause("8.20"));
  }
}

const DataType* SpecializationArgument(const std::vector<DataType>& args,
                                       std::size_t index,
                                       std::string_view name) {
  for (const DataType& arg : args) {
    if (arg.param_arg_name == name) return &arg;
  }
  const bool kNamed = std::ranges::any_of(
      args, [](const DataType& arg) { return !arg.param_arg_name.empty(); });
  return !kNamed && index < args.size() ? &args[index] : nullptr;
}

static std::unordered_map<std::string_view, DataType> SpecializationBindings(
    const ClassDecl& cls, const DataType& type) {
  std::unordered_map<std::string_view, DataType> bound;
  for (std::size_t i = 0; i < cls.params.size(); ++i) {
    const std::string_view kName = cls.params[i].first;
    if (!cls.type_param_names.contains(kName)) continue;
    const DataType* arg = SpecializationArgument(type.type_params, i, kName);
    bound[kName] = arg != nullptr ? *arg : cls.param_types.at(i);
  }
  return bound;
}

void ReportSpecializationOverrideMismatches(const DataType& type, SourceLoc loc,
                                            const CompilationUnit* unit,
                                            const TypedefMap& typedefs,
                                            DiagEngine& diag) {
  const ClassDecl* cls = FindClassDecl(type.type_name, unit);
  if (cls == nullptr || cls->type_param_names.empty()) return;
  const auto kBound = SpecializationBindings(*cls, type);
  for (const ClassMember* m : cls->members) {
    if (m->method == nullptr) continue;
    const OwnedMethod kBase = FindBaseVirtualMethod(cls, m->method->name, unit);
    if (kBase.member == nullptr) continue;
    const auto& base_args = kBase.member->method->func_args;
    const auto& over_args = m->method->func_args;
    const OverrideTypeContext kCtx{kBase.owner, cls, typedefs, unit, &kBound};
    for (size_t i = 0; i < std::min(base_args.size(), over_args.size()); ++i) {
      if (!NamesTypeParameter(over_args[i].data_type, *cls) ||
          !OverrideTypeMismatch(base_args[i].data_type, over_args[i].data_type,
                                false, kCtx)) {
        continue;
      }
      diag.Error(loc,
                 std::format("virtual method override argument '{}' of "
                             "'{}::{}' has mismatched type in this "
                             "specialization",
                             over_args[i].name, cls->name, m->method->name),
                 Subclause("8.20"));
    }
  }
}

void ElaboratorClassRules::ValidateOneMethodOverride(const ClassDecl* cls,
                                                     const ClassMember* m) {
  auto* method = m->method;
  const OwnedMethod kBaseVirtual =
      FindBaseVirtualMethod(cls, method->name, unit_);
  const ClassMember* base_virtual = kBaseVirtual.member;
  if (method->is_method_initial && base_virtual) {
    diag_.Error(method->loc,
                "method with ':initial' shall not override a virtual "
                "base class method",
                Subclause("8.20"));
  }
  if (method->is_method_extends && !base_virtual) {
    diag_.Error(method->loc,
                "method with ':extends' does not override a virtual "
                "base class method",
                Subclause("8.20"));
  }

  if (base_virtual && (base_virtual->is_local != m->is_local ||
                       base_virtual->is_protected != m->is_protected)) {
    diag_.Error(method->loc,
                std::format("virtual method override '{}' is not qualified "
                            "local or protected as the method it overrides is",
                            method->name),
                Subclause("8.20"));
  }

  const auto* base_final = FindBaseFinalMethod(cls, method->name, unit_);
  if (base_final) {
    diag_.Error(method->loc, "cannot override a method declared ':final'",
                Subclause("8.20"));
  }

  if (base_virtual && base_virtual->method) {
    ValidateOverrideSignature(base_virtual->method, method,
                              {kBaseVirtual.owner, cls, typedefs_, unit_},
                              diag_);
  }
}

void ElaboratorClassRules::ValidateVirtualMethodOverrides() {
  for (const auto* cls : AllClassDecls(unit_)) {
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
    const auto* base = FindBaseClass(cls, unit);
    CollectPureVirtualMethods(base, unit, pure_names);
  }
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
    if (m->is_pure_virtual) {
      pure_names.push_back(m->method->name);
    } else {
      std::erase(pure_names, m->method->name);
    }
  }
}

void ElaboratorClassRules::ValidateAbstractClassUnimplemented(
    const ClassDecl* cls) {
  if (cls->is_virtual || cls->is_interface) return;
  std::vector<std::string_view> unimpl;
  CollectPureVirtualMethods(cls, unit_, unimpl);
  for (auto name : unimpl) {
    diag_.Error(cls->range.start,
                std::format("non-abstract class '{}' does not implement "
                            "pure virtual method '{}'",
                            cls->name, name),
                Subclause("8.21"));
  }
}

static void CheckPureFinalMember(const ClassMember* m, DiagEngine& diag) {
  if (m->kind == ClassMemberKind::kMethod && m->method) {
    if (m->is_pure_virtual && m->method->is_method_final) {
      diag.Error(m->method->loc,
                 "':final' shall not be specified on a pure virtual method",
                 Subclause("8.20"));
    }
  } else if (m->kind == ClassMemberKind::kConstraint) {
    if (m->is_pure_virtual && m->is_constraint_final) {
      diag.Error(m->loc, "':final' shall not be specified on a pure constraint",
                 Subclause("18.5.2"));
    }
  }
}

void ElaboratorClassRules::ValidateAbstractClassRules() {
  for (const auto* cls : AllClassDecls(unit_)) {
    for (const auto* m : cls->members) {
      CheckPureFinalMember(m, diag_);
    }
    ValidateAbstractClassUnimplemented(cls);
  }
}

static void CheckInterfaceClassMemberKind(const ClassDecl* cls,
                                          const ClassMember* m,
                                          DiagEngine& diag) {
  if (m->kind == ClassMemberKind::kMethod && m->method &&
      (m->method->is_method_initial || m->method->is_method_extends ||
       m->method->is_method_final)) {
    diag.Error(m->method->loc,
               "dynamic_override_specifiers shall not be used in "
               "an interface class",
               Subclause("8.26.1"));
  }
  if (m->kind == ClassMemberKind::kMethod && !m->is_pure_virtual) {
    diag.Error(m->method ? m->method->loc : cls->range.start,
               std::format("interface class '{}' has a method that is not "
                           "pure virtual",
                           cls->name),
               Subclause("8.26"));
  } else if (m->kind == ClassMemberKind::kProperty && !m->is_param) {
    diag.Error(cls->range.start,
               std::format("interface class '{}' shall not contain "
                           "data members",
                           cls->name),
               Subclause("8.26"));
  } else if (m->kind == ClassMemberKind::kConstraint) {
    diag.Error(cls->range.start,
               std::format("interface class '{}' shall not contain "
                           "constraint blocks",
                           cls->name),
               Subclause("8.26.9"));
  } else if (m->kind == ClassMemberKind::kCovergroup) {
    diag.Error(cls->range.start,
               std::format("interface class '{}' shall not contain "
                           "covergroups",
                           cls->name),
               Subclause("8.26.9"));
  } else if (m->kind == ClassMemberKind::kClassDecl) {
    diag.Error(cls->range.start,
               std::format("interface class '{}' shall not contain "
                           "nested classes",
                           cls->name),
               Subclause("8.26"));
  }
}

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
                 Subclause("8.26.8"));
    }
  }
}

void ElaboratorClassRules::ValidateInterfaceClassMembers(const ClassDecl* cls) {
  ScopeMap method_scope = cu_param_scope_;
  auto add_param = [&](std::string_view pname, const Expr* pexpr) {
    if (pname.empty() || method_scope.count(pname)) return;
    if (auto val = ConstEvalInt(pexpr, method_scope))
      method_scope[pname] = *val;
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

struct InheritanceWording {
  std::string_view verb, noun, self_label;
};
bool ValidateInheritedInterfaceName(const ClassDecl* cls, std::string_view name,
                                    const ClassScope& scope, DiagEngine& diag,
                                    const InheritanceWording& wording) {
  if (cls->type_param_names.count(name) > 0) {
    diag.Error(cls->range.start,
               std::format("{} '{}' names type parameter '{}' where only an "
                           "interface class can be {}",
                           wording.self_label, cls->name, name, wording.noun),
               Subclause("8.26.4"));
    return true;
  }
  if (IsForwardTypedefOnly(name, cls, scope)) {
    diag.Error(cls->range.start,
               std::format("{} '{}' reaches '{}' only through a forward "
                           "typedef, but the interface class's full "
                           "declaration has to precede every {} that {}s it",
                           wording.self_label, cls->name, name,
                           wording.self_label, wording.verb),
               Subclause("8.26.4"));
    return true;
  }
  if (!IsDeclaredBefore(name, cls, scope)) {
    const auto* target = FindClassDecl(name, scope.unit);
    if (target && target->is_interface) {
      diag.Error(cls->range.start,
                 std::format("interface class '{}' has to be declared ahead "
                             "of '{}', which {}s it",
                             name, cls->name, wording.verb),
                 Subclause("8.26.4"));
      return true;
    }
  }
  return false;
}

}  // namespace

void ElaboratorClassRules::ValidateInterfaceClassInheritance(
    const ClassDecl* cls, const ClassScope& scope) {
  if (!cls->implements_types.empty()) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' shall not use "
                            "'implements'",
                            cls->name),
                Subclause("8.26.2"));
  }
  if (cls->base_class.empty()) return;

  ValidateInheritedInterfaceName(cls, cls->base_class, scope, diag_,
                                 {"extend", "extended", "interface class"});
  const auto* base = FindBaseClass(cls, unit_);
  if (base && !base->is_interface) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' cannot extend "
                            "non-interface class '{}'",
                            cls->name, cls->base_class),
                Subclause("8.26.2"));
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
                  Subclause("8.26.2"));
    }
  }
}

void ElaboratorClassRules::BreakClassInheritanceCycles() {
  const SoleClassIndex kClasses(*unit_);
  for (const ClassDecl* cls : AllClassDecls(unit_)) {
    std::unordered_set<const ClassDecl*> seen{cls};
    for (const ClassDecl* c = cls; !c->base_class.empty();) {
      const ClassDecl* found = FindBaseClass(c, unit_);
      c = found != nullptr ? found : kClasses.Find(c->base_class);
      if (c == cls) {
        diag_.Error(cls->range.start,
                    std::format("class '{}' inherits from itself through its "
                                "chain of base classes",
                                cls->name),
                    Subclause("8.13"));
        const_cast<ClassDecl*>(cls)->base_class = {};
        break;
      }
      if (c == nullptr || !seen.insert(c).second) break;
    }
  }
}

void ElaboratorClassRules::ValidateRegularClassInheritance(
    const ClassDecl* cls, const ClassScope& scope) {
  if (!cls->base_class.empty()) {
    const auto* base = FindBaseClass(cls, unit_);
    if (base && base->is_interface) {
      diag_.Error(cls->range.start,
                  std::format("class '{}' cannot extend interface class "
                              "'{}'; use 'implements' instead",
                              cls->name, cls->base_class),
                  Subclause("8.26.2"));
    }
  }
  for (const auto& ref : cls->implements_types) {
    auto impl_name = ref.name;
    if (ValidateInheritedInterfaceName(cls, impl_name, scope, diag_,
                                       {"implement", "implemented", "class"})) {
      continue;
    }
    const auto* impl = FindReferencedClass(ref, unit_);
    if (impl && !impl->is_interface) {
      diag_.Error(cls->range.start,
                  std::format("class '{}' cannot implement non-interface "
                              "class '{}'",
                              cls->name, impl_name),
                  Subclause("8.26.2"));
    }
  }
}

}  // namespace delta
