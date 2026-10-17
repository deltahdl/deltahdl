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

// A method member, with the class declaring it.
struct OwnedMethod {
  const ClassMember* member = nullptr;
  const ClassDecl* owner = nullptr;
};

// What the types of an override and of the method it overrides are read in
// (§8.20): the class declaring each, the design's typedefs and classes, and,
// for a specialization of the overriding class (§8.25), the types it gives
// that class's type parameters; none for the generic declaration.
struct OverrideTypeContext {
  const ClassDecl* base;
  const ClassDecl* derived;
  const TypedefMap& typedefs;
  const CompilationUnit* unit;
  const std::unordered_map<std::string_view, DataType>* bound = nullptr;
};

}  // namespace

// Walks the base-class chain of `cls` (excluding `cls` itself) and returns the
// first method named `method_name` for which `accept` holds, with the class
// declaring it, or nothing.
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

// §6.18 with §6.22.1: the type `type`, written in the class `cls`, stands for,
// a typedef name followed to the type it names: one `cls` declares, then one
// the design's typedef table holds, so a name matches the type it stands for.
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

// Whether `type` names one of the type parameters of `cls`, whose type only a
// specialization of the class gives (§8.25).
static bool NamesTypeParameter(const DataType& type, const ClassDecl& cls) {
  return type.kind == DataTypeKind::kNamed && type.scope_name.empty() &&
         cls.type_param_names.contains(type.type_name);
}

// §8.20: whether the override's type `over` fails to match the overridden
// method's `base`: a matching type (§6.22.1), or, for a return type
// (`is_return`), a class derived from the base's. False where either names a
// type parameter of its class the context gives no type to, which only a
// specialization of the class settles (§8.25).
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

// The type each type parameter of `cls` takes in the specialization `type`:
// the argument it writes for the parameter, or the parameter's default.
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
  // §8.20's rule that `:initial` and `:extends` are mutually exclusive is
  // reported by Parser::ParseDynamicOverrideSpecifiers, which consumes the
  // second specifier without recording it. No source can therefore set both
  // ModuleItem::is_method_initial and ModuleItem::is_method_extends, so this
  // function does not test for the pair.
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

  // §8.20: an override's qualifiers are the prototype's; `virtual` alone may
  // be left off, so the encapsulation qualifiers of §8.18 are what remain.
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

// §8.21 with §8.20 (printed page 197 of IEEE 1800-2023): a method that
// overrides a pure virtual one is its implementation whether or not it is
// declared `virtual`, since a method identified as virtual stays virtual in
// every subclass that overrides it and the keyword there is optional. Only a
// member that is not itself pure takes the name off the list; kept on it for
// want of the keyword, `function int area(); ... endfunction` in a subclass
// of Shape reported Shape's pure area() as unimplemented.
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
  // §8.26: an interface class inherits pure virtual methods from the interfaces
  // it extends; it does not implement them. Only a non-virtual, non-interface
  // class is required to provide implementations.
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
               Subclause("8.26.1"));
  }
  if (m->kind == ClassMemberKind::kMethod && !m->is_pure_virtual) {
    diag.Error(m->method ? m->method->loc : cls->range.start,
               std::format("interface class '{}' has a method that is not "
                           "pure virtual",
                           cls->name),
               Subclause("8.26"));
  } else if (m->kind == ClassMemberKind::kProperty && !m->is_param) {
    // §8.26 (printed page 206): an interface class may contain pure virtual
    // methods, type declarations, and parameter declarations; a
    // parameter/localparam (carried as kProperty with is_param) is not a data
    // member. Syntax 8-3 (printed 208) gives interface_class_item no
    // class_property alternative, so a `const` or a `static` property is a
    // data member like any other; exempting `const` here accepted
    // `const int x = 1;`.
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
                 Subclause("8.26.8"));
    }
  }
}

void ElaboratorClassRules::ValidateInterfaceClassMembers(const ClassDecl* cls) {
  // §8.26.8: a method-argument default is evaluated in the scope that contains
  // the subroutine declaration -- the interface class body. A value parameter
  // or local parameter of the class is a constant visible there by its bare
  // name, so layer the class's own parameters over the compilation-unit
  // parameter scope before checking defaults; otherwise a default naming such a
  // parameter would be wrongly rejected as non-constant.
  ScopeMap method_scope = cu_param_scope_;
  // A parameter whose value is not a constant expression contributes nothing.
  // Substituting zero for it made a method-argument default naming that
  // parameter fold, so §8.26.8 read as satisfied by a default whose value the
  // source never wrote and the elaborator could not compute.
  // RegisterClassParams in elaborator_class_params.cpp reports the parameter
  // itself under §6.20.2, so the breach is named once, at the value that caused
  // it.
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

// §8.13 has a class's superclasses run from the class it extends back to an
// original base class. A chain of extends clauses that returns to a class it
// passed through has no such base, so the class closing the cycle is reported
// and its extends clause is dropped from the tree. A walk from a class off the
// cycle stops where it meets the cycle, which the walk from a class on it
// reports and breaks. A base is looked up as FindBaseClass looks it up and,
// where that finds none, as SoleClassIndex does, which reaches a nested class
// too, so a cycle either lookup would follow is broken.
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
