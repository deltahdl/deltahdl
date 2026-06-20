#include <algorithm>
#include <format>
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

static const ClassMember* FindBaseVirtualMethod(const ClassDecl* cls,
                                                std::string_view method_name,
                                                const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  for (const auto* c = FindClassDecl(cls->base_class, unit); c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kMethod && m->method &&
          m->method->name == method_name &&
          (m->is_virtual || m->is_pure_virtual)) {
        return m;
      }
    }
  }
  return nullptr;
}

static const ClassMember* FindBaseFinalMethod(const ClassDecl* cls,
                                              std::string_view method_name,
                                              const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  for (const auto* c = FindClassDecl(cls->base_class, unit); c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kMethod && m->method &&
          m->method->name == method_name && m->method->is_method_final) {
        return m;
      }
    }
  }
  return nullptr;
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
  if (cls->is_virtual || cls->base_class.empty()) return;
  std::vector<std::string_view> unimpl;
  CollectPureVirtualMethods(cls, unit_, unimpl);
  for (auto name : unimpl) {
    diag_.Error(cls->range.start,
                std::format("non-abstract class '{}' does not implement "
                            "pure virtual method '{}'",
                            cls->name, name));
  }
}

void Elaborator::ValidateAbstractClassRules() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind == ClassMemberKind::kMethod && m->method) {
        if (m->is_pure_virtual && m->method->is_method_final) {
          diag_.Error(
              m->method->loc,
              "':final' shall not be specified on a pure virtual method");
        }
      } else if (m->kind == ClassMemberKind::kConstraint) {
        if (m->is_pure_virtual && m->is_constraint_final) {
          diag_.Error(m->loc,
                      "':final' shall not be specified on a pure constraint");
        }
      }
    }
    ValidateAbstractClassUnimplemented(cls);
  }
}

static const ModuleItem* FindExternPrototype(const ClassDecl* cls,
                                             std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == name && m->method->is_extern) {
      return m->method;
    }
  }
  return nullptr;
}

// §8.24: when an out-of-block declaration repeats a default argument value, it
// shall be syntactically identical to the one in the prototype. The default
// values are parsed into expression trees, so compare those trees node by node
// as a faithful stand-in for syntactic identity.
static bool DefaultArgExprsEqual(const Expr* a, const Expr* b) {
  if (a == nullptr || b == nullptr) return a == b;
  if (a->kind != b->kind || a->op != b->op || a->text != b->text ||
      a->scope_prefix != b->scope_prefix || a->callee != b->callee ||
      a->int_val != b->int_val || a->real_val != b->real_val ||
      a->is_parenthesized != b->is_parenthesized) {
    return false;
  }
  if (!DefaultArgExprsEqual(a->lhs, b->lhs) ||
      !DefaultArgExprsEqual(a->rhs, b->rhs) ||
      !DefaultArgExprsEqual(a->condition, b->condition) ||
      !DefaultArgExprsEqual(a->true_expr, b->true_expr) ||
      !DefaultArgExprsEqual(a->false_expr, b->false_expr) ||
      !DefaultArgExprsEqual(a->base, b->base) ||
      !DefaultArgExprsEqual(a->index, b->index)) {
    return false;
  }
  if (a->args.size() != b->args.size()) return false;
  for (size_t i = 0; i < a->args.size(); ++i) {
    if (!DefaultArgExprsEqual(a->args[i], b->args[i])) return false;
  }
  return true;
}

static void ValidateOutOfBlockSignature(const ModuleItem* proto,
                                        const ModuleItem* impl,
                                        std::string_view class_name,
                                        DiagEngine& diag) {
  if (proto->kind != impl->kind) {
    diag.Error(
        impl->loc,
        std::format(
            "out-of-block declaration for '{}::{}' is a {} but "
            "the prototype is a {}",
            class_name, impl->name,
            impl->kind == ModuleItemKind::kFunctionDecl ? "function" : "task",
            proto->kind == ModuleItemKind::kFunctionDecl ? "function"
                                                         : "task"));
    return;
  }
  const auto& proto_args = proto->func_args;
  const auto& impl_args = impl->func_args;
  if (proto_args.size() != impl_args.size()) {
    diag.Error(impl->loc,
               std::format("out-of-block declaration for '{}::{}' has {} "
                           "argument(s) but the prototype has {}",
                           class_name, impl->name, impl_args.size(),
                           proto_args.size()));
    return;
  }
  for (size_t i = 0; i < proto_args.size(); ++i) {
    if (!TypesMatch(proto_args[i].data_type, impl_args[i].data_type)) {
      diag.Error(impl->loc,
                 std::format("out-of-block declaration for '{}::{}' argument "
                             "'{}' has mismatched type",
                             class_name, impl->name, impl_args[i].name));
    }
    if (proto_args[i].direction != impl_args[i].direction) {
      diag.Error(impl->loc,
                 std::format("out-of-block declaration for '{}::{}' argument "
                             "'{}' has mismatched direction",
                             class_name, impl->name, impl_args[i].name));
    }
    // §8.24: omitting the prototype's default value is allowed, but repeating a
    // default value in the out-of-block declaration requires a syntactically
    // identical default value in the prototype.
    const Expr* impl_default = impl_args[i].default_value;
    if (impl_default != nullptr &&
        !DefaultArgExprsEqual(proto_args[i].default_value, impl_default)) {
      diag.Error(impl->loc,
                 std::format("out-of-block declaration for '{}::{}' argument "
                             "'{}' has a default value that is not "
                             "syntactically identical to the prototype",
                             class_name, impl->name, impl_args[i].name));
    }
  }
  if (proto->kind == ModuleItemKind::kFunctionDecl) {
    auto impl_ret = impl->return_type;
    if (impl_ret.kind == DataTypeKind::kNamed && !impl_ret.scope_name.empty() &&
        impl_ret.scope_name == class_name) {
      impl_ret.scope_name = {};
    }
    if (!TypesMatch(proto->return_type, impl_ret)) {
      diag.Error(impl->loc,
                 std::format("out-of-block declaration for '{}::{}' has "
                             "mismatched return type",
                             class_name, impl->name));
    }
  }
}

static const ModuleDecl* FindInterfaceDecl(std::string_view name,
                                           const CompilationUnit* unit) {
  for (const auto* ifc : unit->interfaces) {
    if (ifc->name == name) return ifc;
  }
  return nullptr;
}

static const ModuleItem* FindInterfaceExternPrototype(const ModuleDecl* ifc,
                                                      std::string_view name) {
  for (const auto* it : ifc->items) {
    if ((it->kind == ModuleItemKind::kFunctionDecl ||
         it->kind == ModuleItemKind::kTaskDecl) &&
        it->is_extern && it->name == name) {
      return it;
    }
  }
  return nullptr;
}

// True when location a strictly precedes location b within the same source
// file. Locations from different files carry no relative order, so they are
// reported as not-preceding to avoid spurious diagnostics.
static bool LocPrecedes(const SourceLoc& a, const SourceLoc& b) {
  if (a.file_id != b.file_id) return false;
  if (a.line != b.line) return a.line < b.line;
  return a.column < b.column;
}

void Elaborator::ValidateOutOfBlockDeclarations() {
  std::unordered_set<std::string> linked;
  for (auto* item : unit_->cu_items) {
    if (item->method_class.empty()) continue;
    bool is_func = (item->kind == ModuleItemKind::kFunctionDecl);
    bool is_task = (item->kind == ModuleItemKind::kTaskDecl);
    if (!is_func && !is_task) continue;
    const auto* cls = FindClassDecl(item->method_class, unit_);
    if (!cls) {
      const auto* ifc = FindInterfaceDecl(item->method_class, unit_);
      if (ifc) {
        const auto* proto = FindInterfaceExternPrototype(ifc, item->name);
        if (!proto) {
          diag_.Error(
              item->loc,
              std::format("no matching extern prototype for '{}.{}' in "
                          "interface '{}'",
                          item->method_class, item->name, item->method_class));
          continue;
        }
        auto key =
            std::string(item->method_class) + "." + std::string(item->name);
        if (linked.count(key)) {
          diag_.Error(item->loc,
                      std::format("duplicate hierarchical body for '{}.{}'",
                                  item->method_class, item->name));
          continue;
        }
        linked.insert(key);
        ValidateOutOfBlockSignature(proto, item, item->method_class, diag_);
        continue;
      }
      diag_.Error(item->loc,
                  std::format("out-of-block declaration for unknown class '{}'",
                              item->method_class));
      continue;
    }
    const auto* proto = FindExternPrototype(cls, item->name);
    if (!proto) {
      diag_.Error(
          item->loc,
          std::format("no matching extern prototype for '{}::{}' in "
                      "class '{}'",
                      item->method_class, item->name, item->method_class));
      continue;
    }
    // §8.24: an out-of-block declaration shall follow the class declaration, so
    // a body that appears ahead of its class in source order is illegal.
    if (LocPrecedes(item->loc, cls->range.start)) {
      diag_.Error(
          item->loc,
          std::format("out-of-block declaration for '{}::{}' shall follow the "
                      "declaration of class '{}'",
                      item->method_class, item->name, item->method_class));
      continue;
    }
    auto key = std::string(item->method_class) + "::" + std::string(item->name);
    if (linked.count(key)) {
      diag_.Error(item->loc,
                  std::format("duplicate out-of-block declaration for '{}::{}'",
                              item->method_class, item->name));
      continue;
    }
    linked.insert(key);
    ValidateOutOfBlockSignature(proto, item, item->method_class, diag_);
  }
}

void Elaborator::ValidateInterfaceClassMembers(const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        (m->method->is_method_initial || m->method->is_method_extends ||
         m->method->is_method_final)) {
      diag_.Error(m->method->loc,
                  "dynamic_override_specifiers shall not be used in "
                  "an interface class");
    }
    if (m->kind == ClassMemberKind::kMethod && !m->is_pure_virtual) {
      diag_.Error(m->method ? m->method->loc : cls->range.start,
                  std::format("interface class '{}' shall only contain "
                              "pure virtual methods",
                              cls->name));
    } else if (m->kind == ClassMemberKind::kProperty && !m->is_const) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' shall not contain "
                              "data members",
                              cls->name));
    } else if (m->kind == ClassMemberKind::kConstraint) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' shall not contain "
                              "constraint blocks",
                              cls->name));
    } else if (m->kind == ClassMemberKind::kCovergroup) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' shall not contain "
                              "covergroups",
                              cls->name));
    } else if (m->kind == ClassMemberKind::kClassDecl) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' shall not contain "
                              "nested classes",
                              cls->name));
    }

    if (m->kind == ClassMemberKind::kMethod && m->method) {
      for (const auto& arg : m->method->func_args) {
        if (arg.default_value &&
            !IsConstantExpr(arg.default_value, cu_param_scope_)) {
          diag_.Error(m->method->loc,
                      std::format("interface class method '{}' argument '{}': "
                                  "default value must be a constant expression",
                                  m->method->name, arg.name));
        }
      }
    }
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

void Elaborator::ValidateInterfaceClassInheritance(const ClassDecl* cls) {
  if (!cls->implements_types.empty()) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' shall not use "
                            "'implements'",
                            cls->name));
  }
  if (cls->base_class.empty()) return;

  if (cls->type_param_names.count(cls->base_class) > 0) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' shall not extend type "
                            "parameter '{}'",
                            cls->name, cls->base_class));
  } else if (IsForwardTypedefOnly(cls->base_class, cls, unit_)) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' shall not extend forward "
                            "typedef '{}'; the interface class must be "
                            "declared before it is extended",
                            cls->name, cls->base_class));
  } else if (!IsDeclaredBefore(cls->base_class, cls, unit_)) {
    const auto* base = FindClassDecl(cls->base_class, unit_);
    if (base && base->is_interface) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' must be declared before "
                              "it is extended by '{}'",
                              cls->base_class, cls->name));
    }
  }

  const auto* base = FindClassDecl(cls->base_class, unit_);
  if (base && !base->is_interface) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' cannot extend "
                            "non-interface class '{}'",
                            cls->name, cls->base_class));
  }
  for (const auto& ref : cls->extends_interfaces) {
    auto iface_name = ref.name;

    if (cls->type_param_names.count(iface_name) > 0) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' shall not extend type "
                              "parameter '{}'",
                              cls->name, iface_name));
      continue;
    }

    if (IsForwardTypedefOnly(iface_name, cls, unit_)) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' shall not extend forward "
                              "typedef '{}'; the interface class must be "
                              "declared before it is extended",
                              cls->name, iface_name));
      continue;
    }

    if (!IsDeclaredBefore(iface_name, cls, unit_)) {
      const auto* ibase = FindClassDecl(iface_name, unit_);
      if (ibase && ibase->is_interface) {
        diag_.Error(cls->range.start,
                    std::format("interface class '{}' must be declared before "
                                "it is extended by '{}'",
                                iface_name, cls->name));
        continue;
      }
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

    if (cls->type_param_names.count(impl_name) > 0) {
      diag_.Error(cls->range.start,
                  std::format("class '{}' shall not implement type "
                              "parameter '{}'",
                              cls->name, impl_name));
      continue;
    }

    if (IsForwardTypedefOnly(impl_name, cls, unit_)) {
      diag_.Error(cls->range.start,
                  std::format("class '{}' shall not implement forward "
                              "typedef '{}'; the interface class must be "
                              "declared before it is implemented",
                              cls->name, impl_name));
      continue;
    }

    if (!IsDeclaredBefore(impl_name, cls, unit_)) {
      const auto* impl = FindClassDecl(impl_name, unit_);
      if (impl && impl->is_interface) {
        diag_.Error(cls->range.start,
                    std::format("interface class '{}' must be declared before "
                                "it is implemented by '{}'",
                                impl_name, cls->name));
        continue;
      }
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
  if (!iface->base_class.empty()) {
    const auto* base = FindClassDecl(iface->base_class, unit);
    if (base && base->is_interface) {
      auto base_key =
          MakeSpecKey(iface->base_class, iface->base_class_type_params);
      CollectInterfacePureVirtualMethods(base, base_key, unit, out, visited);
    }
  }
  for (const auto& ref : iface->extends_interfaces) {
    const auto* ext = FindClassDecl(ref.name, unit);
    if (ext && ext->is_interface) {
      auto ext_key = MakeSpecKey(ref.name, ref.type_params);
      CollectInterfacePureVirtualMethods(ext, ext_key, unit, out, visited);
    }
  }
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

static void ValidateMethodNameConflicts(const ClassDecl* cls,
                                        const CompilationUnit* unit,
                                        DiagEngine& diag) {
  IfaceMethodMap iface_methods;
  std::unordered_set<std::string> visited;

  if (cls->is_interface) {
    if (!cls->base_class.empty()) {
      const auto* base = FindClassDecl(cls->base_class, unit);
      if (base && base->is_interface) {
        auto base_key =
            MakeSpecKey(cls->base_class, cls->base_class_type_params);
        CollectInterfacePureVirtualMethods(base, base_key, unit, iface_methods,
                                           visited);
      }
    }
    for (const auto& ref : cls->extends_interfaces) {
      const auto* ext = FindClassDecl(ref.name, unit);
      if (ext && ext->is_interface) {
        auto ext_key = MakeSpecKey(ref.name, ref.type_params);
        CollectInterfacePureVirtualMethods(ext, ext_key, unit, iface_methods,
                                           visited);
      }
    }
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

  if (!cls->is_interface) {
    for (const auto& [method_name, entries] : iface_methods) {
      const ModuleItem* impl = nullptr;
      for (const auto* cm : cls->members) {
        if (cm->kind == ClassMemberKind::kMethod && cm->method &&
            cm->method->name == method_name &&
            (cm->is_virtual || cm->is_pure_virtual)) {
          impl = cm->method;
          break;
        }
      }
      if (!impl) {
        for (const auto* walk = cls->base_class.empty()
                                    ? nullptr
                                    : FindClassDecl(cls->base_class, unit);
             walk; walk = walk->base_class.empty()
                              ? nullptr
                              : FindClassDecl(walk->base_class, unit)) {
          for (const auto* bm : walk->members) {
            if (bm->kind == ClassMemberKind::kMethod && bm->method &&
                bm->method->name == method_name && bm->is_virtual) {
              impl = bm->method;
              break;
            }
          }
          if (impl) break;
        }
      }
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
}

static bool HasConcreteVirtualMethodInHierarchy(const ClassDecl* cls,
                                                std::string_view method_name,
                                                const CompilationUnit* unit) {
  for (const auto* cm : cls->members) {
    if (cm->kind == ClassMemberKind::kMethod && cm->method &&
        cm->method->name == method_name && cm->is_virtual) {
      return true;
    }
  }
  if (cls->base_class.empty()) return false;
  const auto* walk = FindClassDecl(cls->base_class, unit);
  while (walk) {
    for (const auto* bm : walk->members) {
      if (bm->kind == ClassMemberKind::kMethod && bm->method &&
          bm->method->name == method_name && bm->is_virtual &&
          !bm->is_pure_virtual) {
        return true;
      }
    }
    walk = walk->base_class.empty() ? nullptr
                                    : FindClassDecl(walk->base_class, unit);
  }
  return false;
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
  const auto* walk =
      cls->base_class.empty() ? nullptr : FindClassDecl(cls->base_class, unit);
  while (walk) {
    for (const auto* bm : walk->members) {
      if (bm->kind == ClassMemberKind::kMethod && bm->method &&
          bm->method->name == method_name && bm->is_virtual &&
          !bm->is_pure_virtual) {
        return bm->method;
      }
    }
    walk = walk->base_class.empty() ? nullptr
                                    : FindClassDecl(walk->base_class, unit);
  }
  return nullptr;
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

    const auto& iface_args = im->method->func_args;
    const auto& impl_args = impl->func_args;
    size_t n = std::min(iface_args.size(), impl_args.size());
    for (size_t i = 0; i < n; ++i) {
      bool iface_has = iface_args[i].default_value != nullptr;
      bool impl_has = impl_args[i].default_value != nullptr;
      // §8.26.8: the default argument value of an interface class method must
      // be the same for every class that implements it. A default present on
      // one side but absent on the other cannot yield a common value, so the
      // implementing method's defaults must mirror the interface prototype's.
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
    if (m->kind == ClassMemberKind::kTypedef)
      own_names.insert(m->name);
    else if (m->kind == ClassMemberKind::kProperty)
      own_names.insert(m->name);
  }
}

static void CollectEffectiveParamTypeNames(const ClassDecl* iface,
                                           const std::string& spec_key,
                                           const CompilationUnit* unit,
                                           NameOriginMap& out) {
  std::unordered_set<std::string_view> own_names;
  CollectOwnParamTypeNames(iface, own_names);
  for (auto n : own_names) out[n].insert(spec_key);
  auto inherit = [&](const ClassDecl* parent, const std::string& parent_key) {
    NameOriginMap parent_map;
    CollectEffectiveParamTypeNames(parent, parent_key, unit, parent_map);
    for (const auto& [name, origins] : parent_map) {
      if (own_names.count(name)) continue;
      for (const auto& o : origins) out[name].insert(o);
    }
  };
  if (!iface->base_class.empty()) {
    const auto* base = FindClassDecl(iface->base_class, unit);
    if (base && base->is_interface) {
      auto base_key =
          MakeSpecKey(iface->base_class, iface->base_class_type_params);
      inherit(base, base_key);
    }
  }
  for (const auto& ref : iface->extends_interfaces) {
    const auto* ext = FindClassDecl(ref.name, unit);
    if (ext && ext->is_interface) {
      auto ext_key = MakeSpecKey(ref.name, ref.type_params);
      inherit(ext, ext_key);
    }
  }
}

static void ValidateParamTypeConflicts(const ClassDecl* cls,
                                       const CompilationUnit* unit,
                                       DiagEngine& diag) {
  if (!cls->is_interface) return;
  std::unordered_set<std::string_view> own_names;
  CollectOwnParamTypeNames(cls, own_names);
  NameOriginMap inherited;
  auto process = [&](const ClassDecl* parent, const std::string& parent_key) {
    NameOriginMap parent_map;
    CollectEffectiveParamTypeNames(parent, parent_key, unit, parent_map);
    for (const auto& [name, origins] : parent_map) {
      if (own_names.count(name)) continue;
      for (const auto& o : origins) inherited[name].insert(o);
    }
  };
  if (!cls->base_class.empty()) {
    const auto* base = FindClassDecl(cls->base_class, unit);
    if (base && base->is_interface) {
      auto base_key = MakeSpecKey(cls->base_class, cls->base_class_type_params);
      process(base, base_key);
    }
  }
  for (const auto& ref : cls->extends_interfaces) {
    const auto* ext = FindClassDecl(ref.name, unit);
    if (ext && ext->is_interface) {
      auto ext_key = MakeSpecKey(ref.name, ref.type_params);
      process(ext, ext_key);
    }
  }
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
