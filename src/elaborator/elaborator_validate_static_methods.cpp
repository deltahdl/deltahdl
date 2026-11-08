#include <cstddef>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static bool IsLiteralTypeOfThis(const Expr* e) {
  return e && e->kind == ExprKind::kTypeRef && e->lhs &&
         e->lhs->kind == ExprKind::kIdentifier && e->lhs->text == "this";
}

static bool ExprRefsThisOrSuper(const Expr* e) {
  if (!e) return false;
  if (IsLiteralTypeOfThis(e)) return false;
  if (e->kind == ExprKind::kIdentifier &&
      (e->text == "this" || e->text == "super"))
    return true;
  return AnyExprChild(e, ExprRefsThisOrSuper);
}

static bool StmtRefsThisOrSuper(const Stmt* s) {
  if (!s) return false;
  bool found = false;
  ForEachChildExpr(s, [&found](const Expr* e) {
    if (!found) found = ExprRefsThisOrSuper(e);
  });
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtRefsThisOrSuper(sub);
  });
  return found;
}

static void CollectForHeaderNames(const Stmt* s,
                                  std::unordered_set<std::string_view>& out) {
  for (size_t k = 0; k < s->for_inits.size() && k < s->for_init_types.size();
       ++k) {
    if (s->for_init_types[k].kind == DataTypeKind::kImplicit) continue;
    const Stmt* init = s->for_inits[k];
    if (init && init->lhs && init->lhs->kind == ExprKind::kIdentifier) {
      out.insert(init->lhs->text);
    }
  }
}

std::unordered_set<std::string_view> NamesDeclaredUnder(const Stmt* s) {
  std::unordered_set<std::string_view> declared;
  CollectForHeaderNames(s, declared);
  for (auto v : s->foreach_vars) {
    if (!v.empty()) declared.insert(v);
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (sub && sub->kind == StmtKind::kVarDecl && !sub->var_name.empty()) {
      declared.insert(sub->var_name);
    }
  });
  return declared;
}

static bool IsAccessThroughAHandle(const Expr* e) {
  if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution) {
    return false;
  }
  const Expr* base = e->lhs;
  return base == nullptr || base->kind != ExprKind::kIdentifier ||
         (base->text != "this" && base->text != "super");
}

static bool IsAccessThroughAClassScope(const Expr* e) {
  return e->kind == ExprKind::kMemberAccess && e->is_scope_resolution;
}

static bool ExprRefsNonStaticMember(
    const Expr* e, const std::unordered_set<std::string_view>& non_static,
    const std::unordered_set<std::string_view>& locals) {
  if (!e) return false;
  if (IsAccessThroughAHandle(e) || IsAccessThroughAClassScope(e)) {
    return ExprRefsNonStaticMember(e->lhs, non_static, locals);
  }
  if (e->kind == ExprKind::kIdentifier && non_static.count(e->text) &&
      !locals.count(e->text))
    return true;
  if (e->kind == ExprKind::kCall && !e->callee.empty() &&
      non_static.count(e->callee) && !locals.count(e->callee))
    return true;
  return AnyExprChild(e, [&](const Expr* child) {
    return ExprRefsNonStaticMember(child, non_static, locals);
  });
}

static bool StmtRefsNonStaticMember(
    const Stmt* s, const std::unordered_set<std::string_view>& non_static,
    const std::unordered_set<std::string_view>& locals) {
  if (!s) return false;
  std::unordered_set<std::string_view> declared = NamesDeclaredUnder(s);
  std::unordered_set<std::string_view> widened;
  if (!declared.empty()) {
    widened = locals;
    widened.insert(declared.begin(), declared.end());
  }
  const std::unordered_set<std::string_view>& scope =
      declared.empty() ? locals : widened;

  bool found = false;
  ForEachChildExpr(s, [&](Expr* const& e) {
    if (found) return;
    found = ExprRefsNonStaticMember(e, non_static, scope);
  });
  if (found) return true;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtRefsNonStaticMember(sub, non_static, scope);
  });
  return found;
}

static void CheckStaticMethodsForThisSuper(const ClassDecl* cls,
                                           DiagEngine& diag) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->is_static) continue;
    if (!m->method) continue;
    const ModuleItem* body = MethodBody(m->method);
    for (const auto* s : body->func_body_stmts) {
      if (StmtRefsThisOrSuper(s)) {
        diag.Error(body->loc,
                   "'this' and 'super' shall not be used in "
                   "a static method",
                   Subclause("8.10"));
        break;
      }
    }
  }
}

static std::unordered_set<std::string_view> CollectNonStaticMemberNames(
    const ClassDecl* cls) {
  std::unordered_set<std::string_view> non_static;
  for (const auto* member : cls->members) {
    if (member->is_static || member->is_param) continue;
    if (member->kind == ClassMemberKind::kProperty && !member->name.empty()) {
      non_static.insert(member->name);
    } else if (member->kind == ClassMemberKind::kMethod && member->method &&
               member->method->name != "new") {
      non_static.insert(member->method->name);
    }
  }
  return non_static;
}

std::unordered_set<std::string_view> CollectMethodLocalNames(
    const ModuleItem* method) {
  std::unordered_set<std::string_view> locals;
  for (const auto& arg : method->func_args) {
    if (!arg.name.empty()) locals.insert(arg.name);
  }
  if (method->kind == ModuleItemKind::kFunctionDecl) {
    locals.insert(method->name);
  }
  for (const auto* s : method->func_body_stmts) {
    if (s && s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
      locals.insert(s->var_name);
    }
  }
  return locals;
}

void ElaboratorClassRules::ValidateNestedClassStaticMethods(
    const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kClassDecl && m->nested_class) {
      ValidateOneClassStaticMethods(m->nested_class);
    }
  }
}

void ElaboratorClassRules::ValidateOneClassStaticMethods(const ClassDecl* cls) {
  if (!static_method_bodies_checked_.insert(cls).second) return;
  ValidateNestedClassStaticMethods(cls);
  CheckStaticMethodsForThisSuper(cls, diag_);

  std::unordered_set<std::string_view> non_static =
      CollectNonStaticMemberNames(cls);
  if (non_static.empty()) return;

  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->is_static) continue;
    if (!m->method) continue;

    const ModuleItem* body = MethodBody(m->method);
    std::unordered_set<std::string_view> locals = CollectMethodLocalNames(body);

    for (const auto* s : body->func_body_stmts) {
      if (StmtRefsNonStaticMember(s, non_static, locals)) {
        diag_.Error(body->loc,
                    "static method shall not access non-static members",
                    Subclause("8.10"));
        break;
      }
    }
  }
}

void ElaboratorClassRules::ValidateStaticMethodsAmong(
    const std::vector<ModuleItem*>& items) {
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
      ValidateOneClassStaticMethods(item->class_decl);
    }
  }
}

void ElaboratorClassRules::ValidateStaticMethodBodies(const ModuleDecl* decl) {
  for (const auto* cls : unit_->classes) {
    ValidateOneClassStaticMethods(cls);
  }
  ValidateStaticMethodsAmong(decl->items);
  for (const auto* pkg : unit_->packages) {
    ValidateStaticMethodsAmong(pkg->items);
  }
  for (const auto* prog : unit_->programs) {
    ValidateStaticMethodsAmong(prog->items);
  }
  for (const auto* iface : unit_->interfaces) {
    ValidateStaticMethodsAmong(iface->items);
  }
}

static bool ItemExprRefsThisOrSuper(const ModuleItem* item) {
  return ExprRefsThisOrSuper(item->init_expr) ||
         ExprRefsThisOrSuper(item->assign_lhs) ||
         ExprRefsThisOrSuper(item->assign_rhs);
}

void ElaboratorClassRules::ValidateThisInItem(const ModuleItem* item) {
  bool is_proc = IsProceduralItemKind(item->kind);
  bool in_body = is_proc && item->body && StmtRefsThisOrSuper(item->body);
  if (in_body || ItemExprRefsThisOrSuper(item)) {
    diag_.Error(item->loc,
                "'this' has no object to refer to outside a non-static class "
                "method",
                Subclause("8.11"));
    return;
  }
  bool is_func_or_task = item->kind == ModuleItemKind::kFunctionDecl ||
                         item->kind == ModuleItemKind::kTaskDecl;
  if (!is_func_or_task || item->func_body_stmts.empty()) return;
  if (!item->method_class.empty()) return;
  for (const auto* s : item->func_body_stmts) {
    if (StmtRefsThisOrSuper(s)) {
      diag_.Error(item->loc,
                  "'this' has no object to refer to outside a non-static "
                  "class method",
                  Subclause("8.11"));
      return;
    }
  }
}

void ElaboratorClassRules::ValidateThisOutsideModules() {
  for (const auto* item : unit_->cu_items) ValidateThisInItem(item);
  for (const auto* pkg : unit_->packages) {
    for (const auto* item : pkg->items) ValidateThisInItem(item);
  }
}

void ElaboratorClassRules::ValidateThisUsage(const ModuleDecl* decl) {
  for (const auto* item : decl->items) ValidateThisInItem(item);
}

}  // namespace delta
