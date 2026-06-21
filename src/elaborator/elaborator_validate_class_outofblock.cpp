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

// Compares one prototype argument against the corresponding out-of-block
// declaration argument (type, direction, and repeated default value per §8.24).
static void CheckOutOfBlockArg(const FunctionArg& proto_arg,
                               const FunctionArg& impl_arg,
                               const ModuleItem* impl,
                               std::string_view class_name, DiagEngine& diag) {
  if (!TypesMatch(proto_arg.data_type, impl_arg.data_type)) {
    diag.Error(impl->loc,
               std::format("out-of-block declaration for '{}::{}' argument "
                           "'{}' has mismatched type",
                           class_name, impl->name, impl_arg.name));
  }
  if (proto_arg.direction != impl_arg.direction) {
    diag.Error(impl->loc,
               std::format("out-of-block declaration for '{}::{}' argument "
                           "'{}' has mismatched direction",
                           class_name, impl->name, impl_arg.name));
  }
  // §8.24: omitting the prototype's default value is allowed, but repeating a
  // default value in the out-of-block declaration requires a syntactically
  // identical default value in the prototype.
  const Expr* impl_default = impl_arg.default_value;
  if (impl_default != nullptr &&
      !DefaultArgExprsEqual(proto_arg.default_value, impl_default)) {
    diag.Error(impl->loc,
               std::format("out-of-block declaration for '{}::{}' argument "
                           "'{}' has a default value that is not "
                           "syntactically identical to the prototype",
                           class_name, impl->name, impl_arg.name));
  }
}

static void CheckOutOfBlockReturnType(const ModuleItem* proto,
                                      const ModuleItem* impl,
                                      std::string_view class_name,
                                      DiagEngine& diag) {
  if (proto->kind != ModuleItemKind::kFunctionDecl) return;
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
    CheckOutOfBlockArg(proto_args[i], impl_args[i], impl, class_name, diag);
  }
  CheckOutOfBlockReturnType(proto, impl, class_name, diag);
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

// Handles an out-of-block body whose `method_class` names an interface rather
// than a class. Mirrors the original interface branch exactly.
static void ValidateInterfaceOutOfBlockBody(
    const ModuleDecl* ifc, ModuleItem* item,
    std::unordered_set<std::string>& linked, DiagEngine& diag) {
  const auto* proto = FindInterfaceExternPrototype(ifc, item->name);
  if (!proto) {
    diag.Error(item->loc,
               std::format("no matching extern prototype for '{}.{}' in "
                           "interface '{}'",
                           item->method_class, item->name, item->method_class));
    return;
  }
  auto key = std::string(item->method_class) + "." + std::string(item->name);
  if (linked.count(key)) {
    diag.Error(item->loc, std::format("duplicate hierarchical body for '{}.{}'",
                                      item->method_class, item->name));
    return;
  }
  linked.insert(key);
  ValidateOutOfBlockSignature(proto, item, item->method_class, diag);
}

// Handles an out-of-block body whose `method_class` names a regular class.
// Mirrors the original class branch exactly.
static void ValidateClassOutOfBlockBody(const ClassDecl* cls, ModuleItem* item,
                                        std::unordered_set<std::string>& linked,
                                        DiagEngine& diag) {
  const auto* proto = FindExternPrototype(cls, item->name);
  if (!proto) {
    diag.Error(item->loc,
               std::format("no matching extern prototype for '{}::{}' in "
                           "class '{}'",
                           item->method_class, item->name, item->method_class));
    return;
  }
  // §8.24: an out-of-block declaration shall follow the class declaration, so
  // a body that appears ahead of its class in source order is illegal.
  if (LocPrecedes(item->loc, cls->range.start)) {
    diag.Error(
        item->loc,
        std::format("out-of-block declaration for '{}::{}' shall follow the "
                    "declaration of class '{}'",
                    item->method_class, item->name, item->method_class));
    return;
  }
  auto key = std::string(item->method_class) + "::" + std::string(item->name);
  if (linked.count(key)) {
    diag.Error(item->loc,
               std::format("duplicate out-of-block declaration for '{}::{}'",
                           item->method_class, item->name));
    return;
  }
  linked.insert(key);
  ValidateOutOfBlockSignature(proto, item, item->method_class, diag);
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
        ValidateInterfaceOutOfBlockBody(ifc, item, linked, diag_);
        continue;
      }
      diag_.Error(item->loc,
                  std::format("out-of-block declaration for unknown class '{}'",
                              item->method_class));
      continue;
    }
    ValidateClassOutOfBlockBody(cls, item, linked, diag_);
  }
}

}  // namespace delta
