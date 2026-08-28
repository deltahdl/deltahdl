// §8.10 "Static methods" and §8.11 "This", the two rules deciding what a
// method may name when it has no object handle. §8.10 bars a static method
// from accessing a non-static member or the special `this` handle, and §8.11
// bars `this` outside a non-static class method altogether. Both are answered
// by searching a body for a name, so both need the same two searches and the
// collection of the names that shadow a member; the rest of the class rules
// are in elaborator_validate_class_members.cpp, which the 1000-line cap in
// .github/workflows/deltahdl.yml separated this file from. No symbol crosses
// the cut.

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast.h"

namespace delta {

static bool IsLiteralTypeOfThis(const Expr* e) {
  return e && e->kind == ExprKind::kTypeRef && e->lhs &&
         e->lhs->kind == ExprKind::kIdentifier && e->lhs->text == "this";
}

static bool ExprRefsThisOrSuper(const Expr* e) {
  if (!e) return false;
  // §8.11 lists type(this) as a permitted form alongside non-static class
  // methods, constraints, and covergroups. The cross-reference in §6.23
  // names it as a way to obtain the enclosing class type without evaluating
  // any expression, so the literal form may appear even where a bare 'this'
  // would otherwise be flagged.
  if (IsLiteralTypeOfThis(e)) return false;
  if (e->kind == ExprKind::kIdentifier &&
      (e->text == "this" || e->text == "super"))
    return true;
  if (ExprRefsThisOrSuper(e->lhs) || ExprRefsThisOrSuper(e->rhs) ||
      ExprRefsThisOrSuper(e->base) || ExprRefsThisOrSuper(e->index) ||
      ExprRefsThisOrSuper(e->condition) || ExprRefsThisOrSuper(e->true_expr) ||
      ExprRefsThisOrSuper(e->false_expr) || ExprRefsThisOrSuper(e->with_expr)) {
    return true;
  }
  for (const auto* elem : e->elements) {
    if (ExprRefsThisOrSuper(elem)) return true;
  }
  for (const auto* arg : e->args) {
    if (ExprRefsThisOrSuper(arg)) return true;
  }
  return false;
}

static bool StmtRefsThisOrSuper(const Stmt* s) {
  if (!s) return false;
  if (ExprRefsThisOrSuper(s->lhs)) return true;
  if (ExprRefsThisOrSuper(s->rhs)) return true;
  if (ExprRefsThisOrSuper(s->expr)) return true;
  if (ExprRefsThisOrSuper(s->condition)) return true;
  for (auto* sub : s->stmts) {
    if (StmtRefsThisOrSuper(sub)) return true;
  }
  if (StmtRefsThisOrSuper(s->then_branch)) return true;
  if (StmtRefsThisOrSuper(s->else_branch)) return true;
  if (StmtRefsThisOrSuper(s->body)) return true;
  if (StmtRefsThisOrSuper(s->for_body)) return true;
  for (auto& ci : s->case_items) {
    if (StmtRefsThisOrSuper(ci.body)) return true;
  }
  return false;
}

// §12.7.1 makes a control variable declared in a for header local to the loop,
// so such a name is not the class member it spells. The parser builds no
// StmtKind::kVarDecl for one: parser_stmt.cpp puts `for (int i = 0; ...)` into
// Stmt::for_inits as an assignment and its type into the matching
// Stmt::for_init_types entry (src/parser/ast_stmt.h). An entry whose type is
// DataTypeKind::kImplicit was written `for (i = 0; ...)`, which assigns a
// variable declared elsewhere and declares nothing, so it contributes no name.
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

// §8.10 bars a static method from accessing a non-static member, and a name a
// statement declares is not a member, so it shadows one wherever the
// declaration stands. This collection therefore reaches every position
// ForEachChildStmt in elaborator_validate_internal.h names. Stmt::for_steps is
// descended and holds no name to collect: A.6.8 admits in it an
// operator_assignment, an inc_or_dec_expression or a call and nothing else.
//
// The set is flat and the whole method body shares it, so a name collected
// anywhere shadows the member everywhere in that body. That is wrong for every
// declaration whose scope §12.7 bounds -- a for header's control variable, a
// named block's locals -- and it is an approximation this collection has always
// made rather than one the for-header names introduce. Making the set scoped
// is issue #3315.
static void CollectLocalNames(const Stmt* s,
                              std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    out.insert(s->var_name);
  }
  for (auto v : s->foreach_vars) {
    if (!v.empty()) out.insert(v);
  }
  CollectForHeaderNames(s, out);
  ForEachChildStmt(s, [&](Stmt* const& sub) { CollectLocalNames(sub, out); });
}

static bool ExprRefsNonStaticMember(
    const Expr* e, const std::unordered_set<std::string_view>& non_static,
    const std::unordered_set<std::string_view>& locals) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && non_static.count(e->text) &&
      !locals.count(e->text))
    return true;
  if (e->kind == ExprKind::kCall && !e->callee.empty() &&
      non_static.count(e->callee) && !locals.count(e->callee))
    return true;
  if (ExprRefsNonStaticMember(e->lhs, non_static, locals) ||
      ExprRefsNonStaticMember(e->rhs, non_static, locals) ||
      ExprRefsNonStaticMember(e->base, non_static, locals) ||
      ExprRefsNonStaticMember(e->index, non_static, locals) ||
      ExprRefsNonStaticMember(e->condition, non_static, locals) ||
      ExprRefsNonStaticMember(e->true_expr, non_static, locals) ||
      ExprRefsNonStaticMember(e->false_expr, non_static, locals) ||
      ExprRefsNonStaticMember(e->with_expr, non_static, locals)) {
    return true;
  }
  for (const auto* elem : e->elements) {
    if (ExprRefsNonStaticMember(elem, non_static, locals)) return true;
  }
  for (const auto* arg : e->args) {
    if (ExprRefsNonStaticMember(arg, non_static, locals)) return true;
  }
  return false;
}

static bool StmtRefsNonStaticMember(
    const Stmt* s, const std::unordered_set<std::string_view>& non_static,
    const std::unordered_set<std::string_view>& locals) {
  if (!s) return false;
  if (ExprRefsNonStaticMember(s->lhs, non_static, locals)) return true;
  if (ExprRefsNonStaticMember(s->rhs, non_static, locals)) return true;
  if (ExprRefsNonStaticMember(s->expr, non_static, locals)) return true;
  if (ExprRefsNonStaticMember(s->condition, non_static, locals)) return true;
  // §8.10 makes the access illegal "within the body of a static method" and
  // names no position in that body where it is permitted, so this search looks
  // at every position ForEachChildStmt in elaborator_validate_internal.h names.
  // That list gives the visitor no way to stop, so the first hit is kept in
  // `found` and the recursion runs only while `found` is false.
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtRefsNonStaticMember(sub, non_static, locals);
  });
  return found;
}

// §8.10: "Access to non-static members or to the special this handle within
// the body of a static method is illegal and results in a compiler error."
// Reports the first offending statement in each static method body. §8.11
// states the separate rule about where the 'this' keyword may be used at all,
// which Elaborator::ValidateThisInItem reports below.
static void CheckStaticMethodsForThisSuper(const ClassDecl* cls,
                                           DiagEngine& diag) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->is_static) continue;
    if (!m->method) continue;
    for (const auto* s : m->method->func_body_stmts) {
      if (StmtRefsThisOrSuper(s)) {
        diag.Error(m->method->loc,
                   "'this' and 'super' shall not be used in "
                   "a static method",
                   Subclause("8.10"));
        break;
      }
    }
  }
}

// §8.10: collects the names of all non-static properties and (non-'new')
// methods of the class — the members a static method is forbidden to access.
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

// §8.10: collects names that are local to a static method body (arguments, the
// function's own result name, and declared locals) and so shadow class members.
static std::unordered_set<std::string_view> CollectStaticMethodLocalNames(
    const ModuleItem* method) {
  std::unordered_set<std::string_view> locals;
  for (const auto& arg : method->func_args) {
    if (!arg.name.empty()) locals.insert(arg.name);
  }
  if (method->kind == ModuleItemKind::kFunctionDecl) {
    locals.insert(method->name);
  }
  for (const auto* s : method->func_body_stmts) {
    CollectLocalNames(s, locals);
  }
  return locals;
}

void Elaborator::ValidateOneClassStaticMethods(const ClassDecl* cls) {
  CheckStaticMethodsForThisSuper(cls, diag_);

  std::unordered_set<std::string_view> non_static =
      CollectNonStaticMemberNames(cls);
  if (non_static.empty()) return;

  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->is_static) continue;
    if (!m->method) continue;

    std::unordered_set<std::string_view> locals =
        CollectStaticMethodLocalNames(m->method);

    for (const auto* s : m->method->func_body_stmts) {
      if (StmtRefsNonStaticMember(s, non_static, locals)) {
        diag_.Error(m->method->loc,
                    "static method shall not access non-static members",
                    Subclause("8.10"));
        break;
      }
    }
  }
}

void Elaborator::ValidateStaticMethodBodies(const ModuleDecl* decl) {
  for (const auto* cls : unit_->classes) {
    ValidateOneClassStaticMethods(cls);
  }
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
      ValidateOneClassStaticMethods(item->class_decl);
    }
  }
}

void Elaborator::ValidateThisInItem(const ModuleItem* item) {
  bool is_proc = IsProceduralItemKind(item->kind);
  if (is_proc && item->body && StmtRefsThisOrSuper(item->body)) {
    diag_.Error(item->loc,
                "'this' shall only be used within non-static class methods",
                Subclause("8.11"));
    return;
  }
  bool is_func_or_task = item->kind == ModuleItemKind::kFunctionDecl ||
                         item->kind == ModuleItemKind::kTaskDecl;
  if (!is_func_or_task || item->func_body_stmts.empty()) return;
  for (const auto* s : item->func_body_stmts) {
    if (StmtRefsThisOrSuper(s)) {
      diag_.Error(item->loc,
                  "'this' shall only be used within non-static "
                  "class methods",
                  Subclause("8.11"));
      return;
    }
  }
}

void Elaborator::ValidateThisUsage(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    ValidateThisInItem(item);
  }
}

}  // namespace delta
