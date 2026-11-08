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

using EnclosingProps = std::unordered_map<std::string_view, std::string_view>;

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

DeclaredMembers CollectDeclaredMembers(const ClassDecl* cls,
                                       const CompilationUnit* unit) {
  DeclaredMembers out;
  std::unordered_set<const ClassDecl*> seen;
  for (const auto* c = cls; c != nullptr && seen.insert(c).second;) {
    AddDeclaredMembers(c, out);
    if (c->base_class.empty()) break;
    c = FindBaseClass(c, unit);
  }
  return out;
}

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
