// §8.23 "Class scope resolution operator ::", the rule on what a nested class
// reaches by a bare name. A class declared within a class has lexically scoped,
// unqualified access to the enclosing class's static properties and methods,
// parameters and local parameters, and no implicit handle to an object of the
// enclosing class: a non-static property of it is reachable only through a
// handle the nested class is given, and the subclause's own example marks
// `outerProp = 0;` in a method of `Inner` illegal beside the legal
// `outerStaticProp = 0;` and `h.outerProp = 0;`. deltahdl reported nothing on
// the illegal line and ran the design (#3781).
//
// The search subtracts the same names §8.10's static-method check subtracts,
// through NamesDeclaredUnder and CollectMethodLocalNames in
// elaborator_validate_static_methods.cpp: a formal, a result name and a block's
// declarations are not the property they spell.

#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

// The non-static properties an enclosing class holds against a bare name, each
// mapped to the name of the class that encloses it. A class nested two deep
// has both classes above it as enclosing classes, so the map is carried down
// and the nearer class's declarations take the place of the farther one's.
using EnclosingProps = std::unordered_map<std::string_view, std::string_view>;

// The names `cls` and the classes it extends declare as members, and among
// them the ones whose nearest declaration is a non-static property. A member
// of `cls` is found before the same name in a base, which is the order §8.13
// resolves an inherited name in, so a base's property a derived class
// redeclares static is not held to be non-static.
struct DeclaredMembers {
  std::unordered_set<std::string_view> all;
  std::unordered_set<std::string_view> instance_props;
};

std::string_view MemberName(const ClassMember* m) {
  if (m->kind == ClassMemberKind::kMethod && m->method != nullptr) {
    return m->method->name;
  }
  if (m->kind == ClassMemberKind::kClassDecl && m->nested_class != nullptr) {
    return m->nested_class->name;
  }
  return m->name;
}

void AddDeclaredMembers(const ClassDecl* cls, DeclaredMembers& out) {
  for (const auto* m : cls->members) {
    if (m == nullptr) continue;
    std::string_view name = MemberName(m);
    if (name.empty() || !out.all.insert(name).second) continue;
    if (m->kind == ClassMemberKind::kProperty && !m->is_static &&
        !m->is_param) {
      out.instance_props.insert(name);
    }
  }
}

// The chain is walked with the classes already seen held aside, so a base
// list that comes back to a class it started from ends the walk rather than
// running it forever; ValidateRegularClassInheritance reports that cycle.
DeclaredMembers CollectDeclaredMembers(const ClassDecl* cls,
                                       const CompilationUnit* unit) {
  DeclaredMembers out;
  std::unordered_set<const ClassDecl*> seen;
  for (const auto* c = cls; c != nullptr && seen.insert(c).second;) {
    AddDeclaredMembers(c, out);
    if (c->base_class.empty()) break;
    c = FindClassDecl(c->base_class, unit);
  }
  return out;
}

// The first expression under `e` that names one of `enclosing` by a bare
// identifier, or null. A `.` member access is qualified through whatever its
// left side names, so only that side is searched -- `h.outerProp` is the legal
// access §8.23's example writes -- and a `::` access names a static member or
// a type through the class scope, which the subclause permits. The keys of an
// assignment pattern are member names of the pattern's type rather than
// references, so only the pattern's elements are searched.
const Expr* FirstEnclosingPropRef(
    const Expr* e, const EnclosingProps& enclosing,
    const std::unordered_set<std::string_view>& locals) {
  if (e == nullptr) return nullptr;
  if (e->kind == ExprKind::kIdentifier) {
    if (e->scope_prefix.empty() && enclosing.count(e->text) > 0 &&
        locals.count(e->text) == 0) {
      return e;
    }
    return nullptr;
  }
  if (e->kind == ExprKind::kMemberAccess) {
    if (e->is_scope_resolution) return nullptr;
    return FirstEnclosingPropRef(e->lhs, enclosing, locals);
  }
  const Expr* found = nullptr;
  auto search = [&](const Expr* child) {
    found = FirstEnclosingPropRef(child, enclosing, locals);
    return found != nullptr;
  };
  if (e->kind == ExprKind::kAssignmentPattern) {
    for (const Expr* elem : e->elements) {
      if (search(elem)) break;
    }
    return found;
  }
  AnyExprChild(e, search);
  return found;
}

// The report for a statement whose expressions reach a property of an
// enclosing class by its bare name, at most one per statement and at the
// statement's position, which is where §8.23's example marks the illegal line.
void ReportEnclosingPropRefs(const Stmt* s, const EnclosingProps& enclosing,
                             const std::unordered_set<std::string_view>& locals,
                             std::string_view nested, DiagEngine& diag) {
  const Expr* found = nullptr;
  ForEachChildExpr(s, [&](Expr* const& e) {
    if (found == nullptr) found = FirstEnclosingPropRef(e, enclosing, locals);
  });
  if (found == nullptr) return;
  diag.Error(s->range.start,
             std::format("non-static property '{}' of the enclosing class '{}' "
                         "cannot be accessed unqualified from a method of the "
                         "nested class '{}'; a nested class has no implicit "
                         "handle to an object of the class enclosing it",
                         found->text, enclosing.at(found->text), nested),
             Subclause("8.23"));
}

// Walks the statements of a nested class's method with the names in scope,
// which grow on the way down as §6.21 has a block's declarations visible to
// that block and the ones below it, and never on the way up.
void WalkStmtsForEnclosingProps(
    const Stmt* s, const EnclosingProps& enclosing,
    const std::unordered_set<std::string_view>& locals, std::string_view nested,
    DiagEngine& diag) {
  if (s == nullptr) return;
  std::unordered_set<std::string_view> scope = NamesDeclaredUnder(s);
  if (!scope.empty()) scope.insert(locals.begin(), locals.end());
  const std::unordered_set<std::string_view>& in_scope =
      scope.empty() ? locals : scope;
  ReportEnclosingPropRefs(s, enclosing, in_scope, nested, diag);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForEnclosingProps(sub, enclosing, in_scope, nested, diag);
  });
}

// Checks every method `cls` declares in its body against `enclosing`. A method
// declared out of the class body (§8.24) keeps its statements on an item of
// the enclosing scope rather than on the member, and is not read here.
void CheckMethodsOf(const ClassDecl* cls, const EnclosingProps& enclosing,
                    DiagEngine& diag) {
  for (const auto* m : cls->members) {
    if (m == nullptr || m->kind != ClassMemberKind::kMethod ||
        m->method == nullptr) {
      continue;
    }
    std::unordered_set<std::string_view> locals =
        CollectMethodLocalNames(m->method);
    for (const auto* s : m->method->func_body_stmts) {
      WalkStmtsForEnclosingProps(s, enclosing, locals, cls->name, diag);
    }
  }
}

// Checks the methods of `cls` against `enclosing`, the non-static properties
// of the classes it is nested in, then the classes nested in `cls` against
// those together with the non-static properties of `cls` itself. A name `cls`
// or a base of it declares stands for its own member, whatever kind it is, so
// it is taken out of the map before the methods are read.
void CheckNestedClassMethods(const ClassDecl* cls, EnclosingProps enclosing,
                             const CompilationUnit* unit, DiagEngine& diag) {
  DeclaredMembers declared = CollectDeclaredMembers(cls, unit);
  for (std::string_view name : declared.all) enclosing.erase(name);
  if (!enclosing.empty()) CheckMethodsOf(cls, enclosing, diag);
  for (std::string_view name : declared.instance_props) {
    enclosing.insert_or_assign(name, cls->name);
  }
  for (const auto* m : cls->members) {
    if (m != nullptr && m->kind == ClassMemberKind::kClassDecl &&
        m->nested_class != nullptr) {
      CheckNestedClassMethods(m->nested_class, enclosing, unit, diag);
    }
  }
}

// The classes `items` declares directly. A class nested in one of them is
// reached from its enclosing class by CheckNestedClassMethods, which is what
// knows what encloses it.
void CheckClassesAmong(const std::vector<ModuleItem*>& items,
                       const CompilationUnit* unit, DiagEngine& diag) {
  for (const auto* item : items) {
    if (item != nullptr && item->kind == ModuleItemKind::kClassDecl &&
        item->class_decl != nullptr) {
      CheckNestedClassMethods(item->class_decl, {}, unit, diag);
    }
  }
}

}  // namespace

void ElaboratorClassRules::ValidateNestedClassEnclosingAccess() {
  for (const auto* cls : unit_->classes) {
    CheckNestedClassMethods(cls, {}, unit_, diag_);
  }
  for (const auto* group : {&unit_->modules, &unit_->interfaces,
                            &unit_->programs, &unit_->checkers}) {
    for (const auto* decl : *group)
      CheckClassesAmong(decl->items, unit_, diag_);
  }
  for (const auto* pkg : unit_->packages) {
    CheckClassesAmong(pkg->items, unit_, diag_);
  }
}

}  // namespace delta
