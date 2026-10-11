#include <cstddef>
#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

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

// The declaration a subroutine body was prototyped by, for the two rules that
// state one shall match the other. §8.24 governs a class out-of-block
// declaration and writes the qualified name with the class-scope operator;
// §25.7 governs a subroutine defined for an interface by a hierarchical name
// and writes it with a dot. The comparison below is the same rule in both, so
// the clause to cite and the separator to write are passed in rather than
// decided inside it by asking what kind of declaration this is.
struct OutOfBlockScope {
  std::string_view name;
  std::string_view separator;
  Subclause subclause;
  // §8.24 holds a class's out-of-block declaration to its prototype exactly,
  // argument names included; §25.7 asks an interface's only for the number and
  // the types of the arguments.
  bool compare_names = false;
};

// Compares one prototype argument against the corresponding out-of-block
// declaration argument: type, direction, and, per §8.24, a repeated default
// value.
static void CheckOutOfBlockArg(const FunctionArg& proto_arg,
                               const FunctionArg& impl_arg,
                               const ModuleItem* impl,
                               const OutOfBlockScope& scope, DiagEngine& diag) {
  if (!TypesMatch(proto_arg.data_type, impl_arg.data_type)) {
    diag.Error(
        impl->loc,
        std::format("out-of-block declaration for '{}{}{}' argument "
                    "'{}' has mismatched type",
                    scope.name, scope.separator, impl->name, impl_arg.name),
        scope.subclause);
  }
  if (scope.compare_names && proto_arg.name != impl_arg.name) {
    diag.Error(
        impl->loc,
        std::format("out-of-block declaration for '{}{}{}' names argument "
                    "'{}' where the prototype names it '{}'",
                    scope.name, scope.separator, impl->name, impl_arg.name,
                    proto_arg.name),
        scope.subclause);
  }
  if (proto_arg.direction != impl_arg.direction) {
    diag.Error(
        impl->loc,
        std::format("out-of-block declaration for '{}{}{}' argument "
                    "'{}' has mismatched direction",
                    scope.name, scope.separator, impl->name, impl_arg.name),
        scope.subclause);
  }
  // §8.24: omitting the prototype's default value is allowed, but repeating a
  // default value in the out-of-block declaration requires a syntactically
  // identical default value in the prototype.
  const Expr* impl_default = impl_arg.default_value;
  if (impl_default != nullptr &&
      !DefaultArgExprsEqual(proto_arg.default_value, impl_default)) {
    diag.Error(
        impl->loc,
        std::format("out-of-block declaration for '{}{}{}' argument "
                    "'{}' has a default value that is not "
                    "syntactically identical to the prototype",
                    scope.name, scope.separator, impl->name, impl_arg.name),
        scope.subclause);
  }
}

static void CheckOutOfBlockReturnType(const ModuleItem* proto,
                                      const ModuleItem* impl,
                                      const OutOfBlockScope& scope,
                                      DiagEngine& diag) {
  if (proto->kind != ModuleItemKind::kFunctionDecl) return;
  auto impl_ret = impl->return_type;
  if (impl_ret.kind == DataTypeKind::kNamed && !impl_ret.scope_name.empty() &&
      impl_ret.scope_name == scope.name) {
    impl_ret.scope_name = {};
  }
  if (!TypesMatch(proto->return_type, impl_ret)) {
    diag.Error(impl->loc,
               std::format("out-of-block declaration for '{}{}{}' has "
                           "mismatched return type",
                           scope.name, scope.separator, impl->name),
               scope.subclause);
  }
}

// §8.24 for a class out-of-block declaration and §25.7 for a subroutine defined
// for an interface by a hierarchical name state one rule in the same words.
// §25.7 (printed page 793): a prototype's arguments match the subroutine
// declaration's in number and type.
static void ValidateOutOfBlockSignature(const ModuleItem* proto,
                                        const ModuleItem* impl,
                                        const OutOfBlockScope& scope,
                                        DiagEngine& diag) {
  if (proto->kind != impl->kind) {
    diag.Error(
        impl->loc,
        std::format(
            "out-of-block declaration for '{}{}{}' is a {} but "
            "the prototype is a {}",
            scope.name, scope.separator, impl->name,
            impl->kind == ModuleItemKind::kFunctionDecl ? "function" : "task",
            proto->kind == ModuleItemKind::kFunctionDecl ? "function" : "task"),
        scope.subclause);
    return;
  }
  const auto& proto_args = proto->func_args;
  const auto& impl_args = impl->func_args;
  if (proto_args.size() != impl_args.size()) {
    diag.Error(impl->loc,
               std::format("out-of-block declaration for '{}{}{}' has {} "
                           "argument(s) but the prototype has {}",
                           scope.name, scope.separator, impl->name,
                           impl_args.size(), proto_args.size()),
               scope.subclause);
    return;
  }
  for (size_t i = 0; i < proto_args.size(); ++i) {
    CheckOutOfBlockArg(proto_args[i], impl_args[i], impl, scope, diag);
  }
  CheckOutOfBlockReturnType(proto, impl, scope, diag);
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
                           item->method_class, item->name, item->method_class),
               Subclause("25.7"));
    return;
  }
  auto key = std::string(item->method_class) + "." + std::string(item->name);
  if (linked.count(key)) {
    diag.Error(item->loc,
               std::format("duplicate hierarchical body for '{}.{}'",
                           item->method_class, item->name),
               Subclause("25.7"));
    return;
  }
  linked.insert(key);
  ValidateOutOfBlockSignature(
      proto, item, {item->method_class, ".", Subclause("25.7")}, diag);
}

// §8.24: whether the class `cls` declares a type named `name` (a typedef or a
// nested class) after its member whose method is `proto`. The prototype,
// resolved where it stands, does not see such a type, while the out-of-block
// declaration's header sees every declaration of the class, so the name
// resolves to two different declarations in the two.
static bool ClassTypeDeclaredAfter(const ClassDecl* cls,
                                   const ModuleItem* proto,
                                   std::string_view name) {
  bool after = false;
  for (const auto* m : cls->members) {
    if (m->method == proto) after = true;
    const bool kType = m->typedef_item != nullptr || m->nested_class != nullptr;
    if (kType && m->name == name) return after;
  }
  return false;
}

// §8.24: reports a named type of the out-of-block declaration `impl`, written
// bare or behind its own class's scope, that resolves to a type `cls` declares
// after the prototype `proto` of it.
static void CheckOutOfBlockTypeResolution(const ClassDecl* cls,
                                          const ModuleItem* proto,
                                          const ModuleItem* impl,
                                          DiagEngine& diag) {
  auto check = [&](const DataType& type) {
    const bool kInClass =
        type.scope_name.empty() || type.scope_name == cls->name;
    if (type.kind != DataTypeKind::kNamed || !kInClass ||
        !ClassTypeDeclaredAfter(cls, proto, type.type_name)) {
      return;
    }
    diag.Error(impl->loc,
               std::format("out-of-block declaration for '{}::{}' resolves "
                           "'{}' to the class's own type, declared after the "
                           "prototype, which resolves it elsewhere",
                           cls->name, impl->name, type.type_name),
               Subclause("8.24"));
  };
  check(impl->return_type);
  for (const auto& arg : impl->func_args) check(arg.data_type);
}

// Handles an out-of-block body whose `method_class` names a regular class: it
// is checked against the class's `extern` prototype of it and, once it is the
// one definition of that prototype, linked to it as the method's body
// (MethodBody in elaborator_validate_classes_internal.h).
static void ValidateClassOutOfBlockBody(
    const ClassDecl* cls, ModuleItem* item,
    std::unordered_set<const ModuleItem*>& linked, DiagEngine& diag) {
  const auto* proto = FindExternPrototype(cls, item->name);
  if (!proto) {
    diag.Error(item->loc,
               std::format("no matching extern prototype for '{}::{}' in "
                           "class '{}'",
                           item->method_class, item->name, item->method_class),
               Subclause("8.24"));
    return;
  }
  // §8.24 places an out-of-block declaration after the declaration of its
  // class, so a body that appears ahead of its class in source order is
  // illegal.
  if (LocPrecedes(item->loc, cls->range.start)) {
    diag.Error(
        item->loc,
        std::format("out-of-block declaration for '{}::{}' comes before the "
                    "declaration of class '{}'",
                    item->method_class, item->name, item->method_class),
        Subclause("8.24"));
    return;
  }
  if (!linked.insert(proto).second) {
    diag.Error(item->loc,
               std::format("duplicate out-of-block declaration for '{}::{}'",
                           item->method_class, item->name),
               Subclause("8.24"));
    return;
  }
  const_cast<ModuleItem*>(proto)->out_of_block_body = item;
  ValidateOutOfBlockSignature(
      proto, item, {item->method_class, "::", Subclause("8.24"), true}, diag);
  CheckOutOfBlockTypeResolution(cls, proto, item, diag);
}

// The class named `name` among `classes`, the classes one scope declares
// directly; null where none is. §8.24 has an out-of-block declaration stand in
// the scope of its class's declaration, so the class is looked for there and
// nowhere else.
static const ClassDecl* ClassNamedAmong(
    const std::vector<const ClassDecl*>& classes, std::string_view name) {
  for (const ClassDecl* cls : classes) {
    if (cls->name == name) return cls;
  }
  return nullptr;
}

// The classes `items` declares directly.
static std::vector<const ClassDecl*> ClassesDeclaredAmong(
    const std::vector<ModuleItem*>& items) {
  std::vector<const ClassDecl*> classes;
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kClassDecl) {
      classes.push_back(item->class_decl);
    }
  }
  return classes;
}

namespace {

// The out-of-block declarations of one scope and the classes it declares
// directly, with what a declaration naming none of them is: an error, or, in
// a module, interface, program or checker, a §25.7 subroutine defined for an
// interface port, `task bus.pull()`, which is left to the interface rules.
struct OutOfBlockSite {
  const std::vector<ModuleItem*>* items;
  std::vector<const ClassDecl*> classes;
  bool unknown_is_error;
};

// The prototypes and interface methods the scopes' declarations have linked
// so far, which a second declaration of either is reported against.
struct OutOfBlockLinks {
  std::unordered_set<std::string> interfaces;
  std::unordered_set<const ModuleItem*> prototypes;
};

}  // namespace

// The out-of-block declaration `item` of `site`, which names a class or
// interface by its method_class.
static void ValidateOutOfBlockItem(ModuleItem* item, const OutOfBlockSite& site,
                                   OutOfBlockLinks& links,
                                   const CompilationUnit* unit,
                                   DiagEngine& diag) {
  const auto* cls = ClassNamedAmong(site.classes, item->method_class);
  if (cls != nullptr) {
    ValidateClassOutOfBlockBody(cls, item, links.prototypes, diag);
    return;
  }
  if (!site.unknown_is_error) return;
  const auto* ifc = FindInterfaceDecl(item->method_class, unit);
  if (ifc) {
    ValidateInterfaceOutOfBlockBody(ifc, item, links.interfaces, diag);
    return;
  }
  diag.Error(item->loc,
             std::format("out-of-block declaration for unknown class '{}'",
                         item->method_class),
             Subclause("8.24"));
}

void ElaboratorClassRules::ValidateOutOfBlockDeclarations() {
  std::vector<OutOfBlockSite> sites;
  sites.push_back(
      {&unit_->cu_items, {unit_->classes.begin(), unit_->classes.end()}, true});
  for (const auto* group : {&unit_->modules, &unit_->interfaces,
                            &unit_->programs, &unit_->checkers}) {
    for (const auto* decl : *group) {
      sites.push_back({&decl->items, ClassesDeclaredAmong(decl->items), false});
    }
  }
  for (const auto* pkg : unit_->packages) {
    sites.push_back({&pkg->items, ClassesDeclaredAmong(pkg->items), true});
  }
  OutOfBlockLinks links;
  for (const OutOfBlockSite& site : sites) {
    for (auto* item : *site.items) {
      if (!item->method_class.empty() &&
          (item->kind == ModuleItemKind::kFunctionDecl ||
           item->kind == ModuleItemKind::kTaskDecl)) {
        ValidateOutOfBlockItem(item, site, links, unit_, diag_);
      }
    }
  }
}

}  // namespace delta
