#include <format>
#include <initializer_list>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// Appends the methods of `cls`, and of the classes nested in it, each inside
// `cls` and the classes `around` holds.
void AddClassMethods(const ClassDecl& cls, std::vector<const ClassDecl*> around,
                     std::vector<SubroutineSite>& out) {
  around.insert(around.begin(), &cls);
  for (const ClassMember* m : cls.members) {
    if (m->method != nullptr) out.push_back({m->method, around});
    if (m->nested_class != nullptr) {
      AddClassMethods(*m->nested_class, around, out);
    }
  }
}

// The class whose handle `e` holds where it is a handle variable `names`
// holds, or a property of a class type selected from one, h.next; empty for
// anything else.
std::string_view HandleClassOf(
    const Expr* e, const std::unordered_set<std::string_view>& names,
    const std::unordered_map<std::string_view, std::string_view>& types,
    const CompilationUnit* unit) {
  if (e->kind == ExprKind::kIdentifier) {
    return names.contains(e->text) ? types.at(e->text) : std::string_view();
  }
  if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution) return {};
  const ClassDecl* cls =
      FindClassDecl(HandleClassOf(e->lhs, names, types, unit), unit);
  if (cls == nullptr) return {};
  const ClassMember* m = FindMemberInClass(cls, e->rhs->text, unit);
  if (m == nullptr || !m->unpacked_dims.empty()) return {};
  return FindClassDecl(m->data_type.type_name, unit) != nullptr
             ? m->data_type.type_name
             : std::string_view();
}

// Whether a function the compilation unit, a module, interface, program,
// checker or package declares under `name` returns a class handle.
bool FunctionReturnsClass(std::string_view name, const CompilationUnit* unit) {
  std::vector<const std::vector<ModuleItem*>*> scopes{&unit->cu_items};
  for (const auto* group :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const ModuleDecl* decl : *group) scopes.push_back(&decl->items);
  }
  for (const PackageDecl* pkg : unit->packages) scopes.push_back(&pkg->items);
  for (const auto* items : scopes) {
    for (const ModuleItem* item : *items) {
      if (item->kind == ModuleItemKind::kFunctionDecl && item->name == name &&
          FindClassDecl(item->return_type.type_name, unit) != nullptr) {
        return true;
      }
    }
  }
  return false;
}

// The properties `cls` and the classes it extends, up the chain, declare.
std::vector<const ClassMember*> ChainProperties(const ClassDecl& cls,
                                                const CompilationUnit* unit) {
  std::vector<const ClassMember*> out;
  for (const ClassDecl* c = &cls; c != nullptr;
       c = FindClassDecl(c->base_class, unit)) {
    for (const ClassMember* m : c->members) {
      if (m->kind == ClassMemberKind::kProperty) out.push_back(m);
    }
  }
  return out;
}

}  // namespace

bool IsHandleOperand(
    const Expr* e, const std::unordered_set<std::string_view>& names,
    const std::unordered_map<std::string_view, std::string_view>& types,
    const CompilationUnit* unit) {
  if (e->kind == ExprKind::kSelect) {
    const std::string_view kArray = ExprIdent(e->base);
    return !names.contains(kArray) && types.contains(kArray);
  }
  if (e->kind == ExprKind::kCall) return FunctionReturnsClass(e->callee, unit);
  return !HandleClassOf(e, names, types, unit).empty();
}

std::vector<SubroutineSite> SubroutinesAmong(
    const std::vector<ModuleItem*>& items,
    const std::vector<const ClassDecl*>& classes) {
  std::vector<const ClassDecl*> declared = classes;
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kClassDecl) {
      declared.push_back(item->class_decl);
    }
  }
  std::vector<SubroutineSite> out;
  for (const ClassDecl* cls : declared) AddClassMethods(*cls, {}, out);
  for (const ModuleItem* item : items) {
    if (item->kind != ModuleItemKind::kFunctionDecl &&
        item->kind != ModuleItemKind::kTaskDecl) {
      continue;
    }
    SubroutineSite site{item, {}};
    for (const ClassDecl* cls : declared) {
      if (cls->name == item->method_class) site.inside.push_back(cls);
    }
    out.push_back(site);
  }
  return out;
}

void AddSubroutineHandles(
    const SubroutineSite& site,
    const std::unordered_set<std::string_view>& class_names,
    const CompilationUnit* unit, std::unordered_set<std::string_view>& names,
    std::unordered_map<std::string_view, std::string_view>& types) {
  auto add = [&](std::string_view name, const DataType& type, bool scalar) {
    if (type.kind != DataTypeKind::kNamed ||
        !class_names.contains(type.type_name)) {
      return;
    }
    if (scalar) names.insert(name);
    types[name] = type.type_name;
  };
  if (!site.inside.empty()) {
    for (const ClassMember* m : ChainProperties(*site.inside.front(), unit)) {
      add(m->name, m->data_type, m->unpacked_dims.empty());
    }
  }
  for (const FunctionArg& arg : site.sub->func_args) {
    add(arg.name, arg.data_type, arg.unpacked_dims.empty());
  }
  // §13.4.1: a function's name is a variable of its return type in its body,
  // `get_next = next;` in §8.13's LinkedPacket.
  if (site.sub->kind == ModuleItemKind::kFunctionDecl) {
    add(site.sub->name, site.sub->return_type,
        site.sub->return_array_dims.empty());
  }
}

// §8.4 over the subroutine bodies among `items` and `classes`, each with the
// handle variables its scope and its own declarations give it.
void ElaboratorClassRules::WalkSubroutinesForClassHandleOps(
    const std::vector<ModuleItem*>& items,
    const std::vector<const ClassDecl*>& classes) {
  for (const SubroutineSite& site : SubroutinesAmong(items, classes)) {
    const auto kNames = class_var_names_;
    const auto kTypes = class_var_types_;
    AddSubroutineHandles(site, class_names_, unit_, class_var_names_,
                         class_var_types_);
    for (const Stmt* s : site.sub->func_body_stmts) {
      WalkStmtsForClassHandleOps(s);
    }
    class_var_names_ = kNames;
    class_var_types_ = kTypes;
  }
}

// §8.17 with §8.18: a subclass's constructor calls its base's, written or
// inserted (§8.15), and a local constructor is visible in no subclass, so a
// class extending one whose constructor is local is reported; NOTE 1 of §8.17
// draws the consequence that such a class cannot be extended.
void ElaboratorClassRules::ValidateLocalConstructorBases() {
  for (const ClassDecl* cls : AllClassDecls(unit_)) {
    const ClassDecl* base = FindClassDecl(cls->base_class, unit_);
    if (base == nullptr) continue;
    for (const ClassMember* m : base->members) {
      if (m->method != nullptr && m->method->name == "new" && m->is_local) {
        diag_.Error(cls->range.start,
                    std::format("class '{}' extends '{}', whose constructor "
                                "is local and so is reached by no subclass",
                                cls->name, base->name),
                    Subclause("8.18"));
      }
    }
  }
}

// §8.4 over the compilation unit's and each package's subroutines and
// classes, read once, where a module's are read with each module.
void ElaboratorClassRules::ValidateClassHandleOpsOutsideModules() {
  WalkSubroutinesForClassHandleOps(
      unit_->cu_items, {unit_->classes.begin(), unit_->classes.end()});
  for (const auto* pkg : unit_->packages) {
    WalkSubroutinesForClassHandleOps(pkg->items);
  }
}

}  // namespace delta
