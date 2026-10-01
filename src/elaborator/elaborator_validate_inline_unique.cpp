#include <memory>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_class_constraints.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// The most typedefs one type is followed through. §6.18 gives no typedef its
// own name as its type, so a chain this long is never written; the bound keeps
// a malformed one from holding the walk.
constexpr int kMaxTypedefHops = 16;

// One scope of the walk, linked to the scope enclosing it. A class body names
// its class in `cls`, and its members are found through the class and its
// bases. Any other scope -- the compilation unit, a module, package, generate
// block, subroutine or statement -- maps each name it declares to the type
// written for it, a function's being its return type; each typedef it
// declares to the type it names; each instance it holds to the module that
// instance instantiates; and keeps the package imports it holds.
struct Scope {
  explicit Scope(const Scope* enclosing, const ClassDecl* body = nullptr)
      : outer(enclosing), cls(body) {}

  const Scope* outer = nullptr;
  const ClassDecl* cls = nullptr;
  std::unordered_map<std::string_view, const DataType*> names;
  std::unordered_map<std::string_view, const DataType*> types;
  std::unordered_map<std::string_view, std::string_view> instances;
  std::vector<const ImportItem*> imports;
};

// The classes enclosing `s`, outermost first, which a type name written in `s`
// reaches before the classes of the unit (§8.23).
std::vector<const ClassDecl*> EnclosingClasses(const Scope* s) {
  std::vector<const ClassDecl*> chain;
  for (; s != nullptr; s = s->outer) {
    if (s->cls != nullptr) chain.insert(chain.begin(), s->cls);
  }
  return chain;
}

// Records in `scope` what `item` declares. A forward typedef, `typedef class
// C;`, names a type declared elsewhere rather than giving one, so it is left
// out of the typedefs a scope declares.
void DeclareItem(const ModuleItem& item, Scope& scope) {
  switch (item.kind) {
    case ModuleItemKind::kVarDecl:
      scope.names[item.name] = &item.data_type;
      break;
    case ModuleItemKind::kFunctionDecl:
      if (item.method_class.empty()) scope.names[item.name] = &item.return_type;
      break;
    case ModuleItemKind::kTypedef:
      if (item.forward_type_kind == DataTypeKind::kImplicit) {
        scope.types[item.name] = &item.typedef_type;
      }
      break;
    case ModuleItemKind::kModuleInst:
      scope.instances[item.inst_name] = item.inst_module;
      break;
    case ModuleItemKind::kImportDecl:
      scope.imports.push_back(&item.import_item);
      break;
    default:
      break;
  }
}

void DeclareItems(const std::vector<ModuleItem*>& items, Scope& scope) {
  for (const auto* item : items) {
    if (item != nullptr) DeclareItem(*item, scope);
  }
}

bool IsGenerateConstruct(ModuleItemKind kind) {
  return kind == ModuleItemKind::kGenerateFor ||
         kind == ModuleItemKind::kGenerateIf ||
         kind == ModuleItemKind::kGenerateCase;
}

// §18.7 reads the names of an inline constraint block first in the class of
// the object randomize() is called on, so a uniqueness group there is checked
// against that class: the static type of the receiver, read in the scope the
// call stands in. A name takes the type of its innermost declaration, or of a
// package variable a scope imports (§26.3), with each typedef followed to the
// type it names (§6.18). A `.` or `::` access takes the declared type of the
// property or method it names in the class on its left (§8.4, §8.9), the
// declaration a package names after `p::` (§26.3), or the declaration an
// instance's module holds after the instance's name (§23.6). A call takes the
// type of what it calls, and a select the element class of the array of
// handles it selects from (§7.4). An array and its elements are not told
// apart, since randomize() is called on an element alone.
class InlineUniqueWalk {
 public:
  InlineUniqueWalk(const CompilationUnit* unit, DiagEngine& diag)
      : unit_(unit), diag_(diag), unit_scope_(nullptr) {}

  void Run() {
    VisitItems(unit_->cu_items, unit_scope_);
    for (const auto* cls : unit_->classes) VisitClass(cls, unit_scope_);
    for (const auto* group : {&unit_->modules, &unit_->interfaces,
                              &unit_->programs, &unit_->checkers}) {
      for (const auto* decl : *group) {
        Scope scope(&unit_scope_);
        DeclarePorts(decl, scope);
        VisitItems(decl->items, scope);
      }
    }
    for (const auto* pkg : unit_->packages) {
      Scope scope(&unit_scope_);
      VisitItems(pkg->items, scope);
    }
  }

 private:
  static void DeclarePorts(const ModuleDecl* decl, Scope& scope) {
    for (const auto& port : decl->ports) {
      scope.names[port.name] = &port.data_type;
    }
  }

  // The module, interface or program named `name`.
  const ModuleDecl* FindModule(std::string_view name) const {
    const ModuleDecl* found = nullptr;
    for (const auto* group :
         {&unit_->modules, &unit_->interfaces, &unit_->programs}) {
      for (const auto* decl : *group) {
        if (decl->name == name) found = decl;
      }
    }
    return found;
  }

  // The declarations of `decl`, which a hierarchical name through one of its
  // instances reads (§23.6), built once per module.
  const Scope& ModuleScope(const ModuleDecl* decl) const {
    auto& slot = module_scopes_[decl];
    if (slot == nullptr) {
      slot = std::make_unique<Scope>(&unit_scope_);
      DeclarePorts(decl, *slot);
      DeclareItems(decl->items, *slot);
    }
    return *slot;
  }

  // The declarations of the package named `name`, which `name::` and an
  // import of it read (§26.3), built once per package. Read from outside, a
  // package holds its own declarations alone, so the scope has no outer one.
  const Scope& PackageScope(std::string_view name) const {
    auto& slot = package_scopes_[name];
    if (slot == nullptr) {
      slot = std::make_unique<Scope>(nullptr);
      for (const auto* pkg : unit_->packages) {
        if (pkg->name == name) DeclareItems(pkg->items, *slot);
      }
    }
    return *slot;
  }

  // The type the typedef named `name` gives, read from `s` outward: a typedef
  // of a class body among the class's members, and any other among those its
  // scope declares.
  const DataType* TypedefIn(std::string_view name, const Scope* s) const {
    for (; s != nullptr; s = s->outer) {
      if (s->cls != nullptr) {
        const ClassMember* m = FindMemberInClass(s->cls, name, unit_);
        if (m != nullptr && m->kind == ClassMemberKind::kTypedef &&
            m->typedef_item->forward_type_kind == DataTypeKind::kImplicit) {
          return &m->typedef_item->typedef_type;
        }
        continue;
      }
      auto it = s->types.find(name);
      if (it != s->types.end()) return it->second;
    }
    return nullptr;
  }

  // The class a type written in `s` holds a handle to, where `chain` is the
  // classes enclosing it, with each typedef its name passes through followed.
  const ClassDecl* TypeClass(const DataType* type, const Scope* s,
                             const std::vector<const ClassDecl*>& chain) const {
    for (int hops = 0;
         hops < kMaxTypedefHops && type->kind == DataTypeKind::kNamed &&
         type->scope_name.empty();
         ++hops) {
      const DataType* aliased = TypedefIn(type->type_name, s);
      if (aliased == nullptr) break;
      type = aliased;
    }
    return ClassOfDeclaredType(*type, chain, unit_);
  }

  // The class a member holds a handle to: a property's declared type, or the
  // return type of a method.
  const ClassDecl* MemberClass(
      const ClassMember* m, const Scope* s,
      const std::vector<const ClassDecl*>& chain) const {
    if (m == nullptr) return nullptr;
    return TypeClass(
        m->method != nullptr ? &m->method->return_type : &m->data_type, s,
        chain);
  }

  // The class `this` or `super` names in `s`: that of the innermost class
  // body, or the class it extends.
  const ClassDecl* SelfClass(std::string_view name, const Scope* s) const {
    for (; s != nullptr; s = s->outer) {
      if (s->cls != nullptr) {
        return name == "super" ? FindClassDecl(s->cls->base_class, unit_)
                               : s->cls;
      }
    }
    return nullptr;
  }

  // The class of the package variable `name` an import of `s` makes visible:
  // an explicit import of that name, or a wildcard import of a package
  // declaring it.
  const ClassDecl* ImportedClass(std::string_view name, const Scope* s) const {
    for (const ImportItem* imp : s->imports) {
      if (imp->is_wildcard || imp->item_name == name) {
        const Scope& pkg = PackageScope(imp->package_name);
        auto it = pkg.names.find(name);
        if (it != pkg.names.end()) return TypeClass(it->second, &pkg, {});
      }
    }
    return nullptr;
  }

  const ClassDecl* NameClass(std::string_view name, const Scope* s) const {
    if (name == "this" || name == "super") return SelfClass(name, s);
    for (; s != nullptr; s = s->outer) {
      if (s->cls != nullptr) {
        const ClassMember* m = FindMemberInClass(s->cls, name, unit_);
        if (m != nullptr) return MemberClass(m, s, EnclosingClasses(s));
        continue;
      }
      auto it = s->names.find(name);
      if (it != s->names.end()) {
        return TypeClass(it->second, s, EnclosingClasses(s));
      }
      if (const ClassDecl* imported = ImportedClass(name, s)) return imported;
    }
    return nullptr;
  }

  // The module `e` names as an instance: an instance a scope from `s` outward
  // holds, an element of an array of instances, or an instance inside the
  // module of another.
  const ModuleDecl* InstanceOf(const Expr* e, const Scope* s) const {
    if (e->kind == ExprKind::kSelect) return InstanceOf(e->base, s);
    if (e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution) {
      const ModuleDecl* outer = InstanceOf(e->lhs, s);
      return outer == nullptr ? nullptr
                              : InstanceOf(e->rhs, &ModuleScope(outer));
    }
    for (; s != nullptr; s = s->outer) {
      auto it = s->instances.find(e->text);
      if (it != s->instances.end()) return FindModule(it->second);
    }
    return nullptr;
  }

  const ClassDecl* AccessClass(const Expr* access, const Scope* s) const {
    std::vector<const ClassDecl*> chain;
    if (access->is_scope_resolution) {
      chain = ClassChainOfScopePrefix(access->lhs, unit_);
      if (chain.empty()) {
        return NameClass(access->rhs->text, &PackageScope(access->lhs->text));
      }
    } else if (const ModuleDecl* inst = InstanceOf(access->lhs, s)) {
      return NameClass(access->rhs->text, &ModuleScope(inst));
    } else if (const ClassDecl* object = Resolve(access->lhs, s)) {
      chain = {object};
    }
    if (chain.empty()) return nullptr;
    const Scope kOwner(&unit_scope_, chain.back());
    return MemberClass(
        FindMemberInClass(chain.back(), access->rhs->text, unit_), &kOwner,
        chain);
  }

  // An expression of a kind not read here -- a conditional, a cast, a system
  // name -- is looked up by its text, which names no declaration in any scope
  // the walk keeps, so it resolves to no class as an identifier naming nothing
  // does.
  const ClassDecl* Resolve(const Expr* e, const Scope* s) const {
    if (e->kind == ExprKind::kSelect) return Resolve(e->base, s);
    if (e->kind == ExprKind::kCall) return Resolve(e->lhs, s);
    if (e->kind == ExprKind::kMemberAccess) return AccessClass(e, s);
    return NameClass(e->text, s);
  }

  // The class randomize() with is called on: the receiver's for
  // `h.randomize()`, and for a bare `randomize()` that of the method it stands
  // in, which §18.6.1 calls on the object the method runs on. Outside every
  // class, and as `std::randomize()`, the call is the scope randomize of
  // §18.12, whose names are no class's.
  const ClassDecl* ReceiverClass(const Expr* call, const Scope& s) const {
    const Expr* callee = call->lhs;
    if (callee->kind == ExprKind::kMemberAccess &&
        !callee->is_scope_resolution && callee->rhs->text == "randomize") {
      return Resolve(callee->lhs, &s);
    }
    if (callee->kind == ExprKind::kIdentifier && callee->text == "randomize") {
      return SelfClass("this", &s);
    }
    return nullptr;
  }

  void VisitExpr(const Expr* e, const Scope& s) {
    if (e == nullptr) return;
    if (e->kind == ExprKind::kCall && e->inline_constraint != nullptr &&
        e->lhs != nullptr) {
      if (const ClassDecl* cls = ReceiverClass(e, s)) {
        ValidateInlineUniqueGroups(e, cls, unit_, diag_);
      }
    }
    ForEachExprChild(e, [&](const Expr* child) { VisitExpr(child, s); });
  }

  // A statement opens a scope holding the variables its own statements
  // declare, a block's items or a for loop's initializations among them, which
  // its expressions and statements read before the enclosing scope.
  void VisitStmt(const Stmt* st, const Scope& outer) {
    if (st == nullptr) return;
    Scope scope(&outer);
    ForEachChildStmt(st, [&](const Stmt* sub) {
      if (sub != nullptr && sub->kind == StmtKind::kVarDecl) {
        scope.names[sub->var_name] = &sub->var_decl_type;
      }
    });
    ForEachChildExpr(st, [&](const Expr* e) { VisitExpr(e, scope); });
    ForEachChildStmt(st, [&](const Stmt* sub) { VisitStmt(sub, scope); });
  }

  // A function or task reads its arguments and the variables its body
  // declares first. A body written out of its class's block (§8.24) is read
  // in that class's scope, as a body written inside it is.
  void VisitSubroutine(const ModuleItem* item, const Scope& outer) {
    Scope owner(&outer);
    if (!item->method_class.empty()) {
      owner.cls = FindClassDecl(item->method_class, unit_);
    }
    Scope scope(&owner);
    for (const auto& arg : item->func_args) {
      scope.names[arg.name] = &arg.data_type;
    }
    for (const Stmt* st : item->func_body_stmts) {
      if (st != nullptr && st->kind == StmtKind::kVarDecl) {
        scope.names[st->var_name] = &st->var_decl_type;
      }
    }
    for (const Stmt* st : item->func_body_stmts) VisitStmt(st, scope);
    VisitStmt(item->body, scope);
  }

  void VisitClass(const ClassDecl* cls, const Scope& outer) {
    Scope scope(&outer, cls);
    for (const auto* m : cls->members) {
      if (m->kind == ClassMemberKind::kMethod && m->method != nullptr) {
        VisitSubroutine(m->method, scope);
      } else if (m->kind == ClassMemberKind::kClassDecl &&
                 m->nested_class != nullptr) {
        VisitClass(m->nested_class, scope);
      }
    }
  }

  // The items of the unit, a module, a package or a generate block, read in a
  // scope holding their own declarations.
  void VisitItems(const std::vector<ModuleItem*>& items, Scope& scope) {
    DeclareItems(items, scope);
    for (const auto* item : items) {
      if (item != nullptr) VisitItem(item, scope);
    }
  }

  void VisitGenerateBlock(const std::vector<ModuleItem*>& items,
                          const Scope& outer) {
    Scope scope(&outer);
    VisitItems(items, scope);
  }

  void VisitItem(const ModuleItem* item, const Scope& s) {
    if (item->kind == ModuleItemKind::kClassDecl &&
        item->class_decl != nullptr) {
      VisitClass(item->class_decl, s);
    } else if (item->kind == ModuleItemKind::kFunctionDecl ||
               item->kind == ModuleItemKind::kTaskDecl) {
      VisitSubroutine(item, s);
    } else if (IsGenerateConstruct(item->kind)) {
      for (const ModuleItem* g = item; g != nullptr; g = g->gen_else) {
        VisitGenerateBlock(g->gen_body, s);
        for (const auto& ci : g->gen_case_items) {
          VisitGenerateBlock(ci.body, s);
        }
      }
    } else {
      VisitExpr(item->init_expr, s);
      VisitExpr(item->assign_rhs, s);
      VisitStmt(item->body, s);
    }
  }

  const CompilationUnit* unit_;
  DiagEngine& diag_;
  Scope unit_scope_;
  mutable std::unordered_map<const ModuleDecl*, std::unique_ptr<Scope>>
      module_scopes_;
  mutable std::unordered_map<std::string_view, std::unique_ptr<Scope>>
      package_scopes_;
};

}  // namespace

void ValidateInlineUniqueReceivers(const CompilationUnit* unit,
                                   DiagEngine& diag) {
  InlineUniqueWalk(unit, diag).Run();
}

}  // namespace delta
