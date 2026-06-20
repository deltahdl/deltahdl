#include <format>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
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

static void CollectLocalNames(const Stmt* s,
                              std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    out.insert(s->var_name);
  }
  for (auto* fi : s->for_inits) CollectLocalNames(fi, out);
  for (auto v : s->foreach_vars) {
    if (!v.empty()) out.insert(v);
  }
  for (auto* sub : s->stmts) CollectLocalNames(sub, out);
  CollectLocalNames(s->then_branch, out);
  CollectLocalNames(s->else_branch, out);
  CollectLocalNames(s->body, out);
  CollectLocalNames(s->for_body, out);
  for (auto& ci : s->case_items) CollectLocalNames(ci.body, out);
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
  for (auto* sub : s->stmts) {
    if (StmtRefsNonStaticMember(sub, non_static, locals)) return true;
  }
  if (StmtRefsNonStaticMember(s->then_branch, non_static, locals)) return true;
  if (StmtRefsNonStaticMember(s->else_branch, non_static, locals)) return true;
  if (StmtRefsNonStaticMember(s->body, non_static, locals)) return true;
  if (StmtRefsNonStaticMember(s->for_body, non_static, locals)) return true;
  for (auto& ci : s->case_items) {
    if (StmtRefsNonStaticMember(ci.body, non_static, locals)) return true;
  }
  return false;
}

// §8.11: a static method shall not reference 'this' or 'super'. Reports the
// first offending statement in each static method body.
static void CheckStaticMethodsForThisSuper(const ClassDecl* cls,
                                           DiagEngine& diag) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->is_static) continue;
    if (!m->method) continue;
    for (const auto* s : m->method->func_body_stmts) {
      if (StmtRefsThisOrSuper(s)) {
        diag.Error(m->method->loc,
                   "'this' and 'super' shall not be used in "
                   "a static method");
        break;
      }
    }
  }
}

// §8.11: collects the names of all non-static properties and (non-'new')
// methods of the class — the members a static method is forbidden to access.
static std::unordered_set<std::string_view> CollectNonStaticMemberNames(
    const ClassDecl* cls) {
  std::unordered_set<std::string_view> non_static;
  for (const auto* member : cls->members) {
    if (member->is_static) continue;
    if (member->kind == ClassMemberKind::kProperty && !member->name.empty()) {
      non_static.insert(member->name);
    } else if (member->kind == ClassMemberKind::kMethod && member->method &&
               member->method->name != "new") {
      non_static.insert(member->method->name);
    }
  }
  return non_static;
}

// §8.11: collects names that are local to a static method body (arguments, the
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
                    "static method shall not access non-static members");
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
  bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                 item->kind == ModuleItemKind::kInitialBlock;
  if (is_proc && item->body && StmtRefsThisOrSuper(item->body)) {
    diag_.Error(item->loc,
                "'this' shall only be used within non-static class methods");
    return;
  }
  bool is_func_or_task = item->kind == ModuleItemKind::kFunctionDecl ||
                         item->kind == ModuleItemKind::kTaskDecl;
  if (!is_func_or_task || item->func_body_stmts.empty()) return;
  for (const auto* s : item->func_body_stmts) {
    if (StmtRefsThisOrSuper(s)) {
      diag_.Error(item->loc,
                  "'this' shall only be used within non-static "
                  "class methods");
      return;
    }
  }
}

void Elaborator::ValidateThisUsage(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    ValidateThisInItem(item);
  }
}

void Elaborator::ValidateFinalClassExtension() {
  auto check = [&](const ClassDecl* cls) {
    if (cls->base_class.empty()) return;

    if (cls->base_class == "process") {
      diag_.Error(cls->range.start, "cannot extend a class declared ':final'");
      return;
    }
    const auto* base = FindClassDecl(cls->base_class, unit_);
    if (base && base->is_final) {
      diag_.Error(cls->range.start, "cannot extend a class declared ':final'");
    }
  };
  for (const auto* cls : unit_->classes) {
    check(cls);
  }
}

// §8.30.1: a weak_reference incorporated into another object as a class
// property carries the same parameter restriction as a standalone variable or a
// subroutine argument — its type argument shall name a class type. Any other
// type argument is a compile error, mirroring the variable-declaration and
// subroutine-argument checks elsewhere in the elaborator.
void Elaborator::ValidateWeakReferenceMembers() {
  auto check_member = [&](const ClassMember* m) {
    if (m->kind != ClassMemberKind::kProperty) return;
    if (m->data_type.kind != DataTypeKind::kNamed) return;
    if (m->data_type.type_name != "weak_reference") return;
    if (m->data_type.type_params.empty()) return;
    const auto& tp = m->data_type.type_params[0];
    if (tp.kind != DataTypeKind::kNamed || !class_names_.count(tp.type_name)) {
      diag_.Error(m->loc,
                  "weak_reference type parameter shall be a class type");
    }
  };
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      check_member(m);
    }
  }
}

static bool IsSuperNewCall(const Stmt* s) {
  if (!s || s->kind != StmtKind::kExprStmt || !s->expr) return false;
  const auto* call = s->expr;
  if (call->kind != ExprKind::kCall) return false;
  const auto* callee = call->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return false;
  bool lhs_is_super = callee->lhs &&
                      callee->lhs->kind == ExprKind::kIdentifier &&
                      callee->lhs->text == "super";
  bool rhs_is_new = callee->rhs && callee->rhs->kind == ExprKind::kIdentifier &&
                    callee->rhs->text == "new";
  return lhs_is_super && rhs_is_new;
}

void Elaborator::ValidateOneClassChainingCtor(const ClassDecl* cls) {
  if (cls->base_class.empty()) return;
  const ClassMember* ctor = nullptr;
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      ctor = m;
      break;
    }
  }
  if (!ctor || !ctor->method) return;
  bool has_super_new = false;
  const auto& stmts = ctor->method->func_body_stmts;
  for (size_t i = 0; i < stmts.size(); ++i) {
    if (!IsSuperNewCall(stmts[i])) continue;
    has_super_new = true;
    if (i != 0) {
      diag_.Error(stmts[i]->range.start,
                  "super.new() shall be the first executable statement "
                  "in the constructor");
    }
    break;
  }
  if (has_super_new &&
      (!cls->extends_args.empty() || cls->extends_has_default)) {
    diag_.Error(ctor->method->loc,
                "constructor shall not contain super.new() when extends "
                "specifier has arguments");
  }
}

// §19.4: a covergroup declared inside a class is an embedded covergroup whose
// identifier names an implicitly declared instance variable. That variable is
// instantiated by assigning the result of new() to it inside the enclosing
// class's new() method, and the standard requires it not be assigned anywhere
// outside that constructor. Any assignment to the covergroup identifier from
// another method of the same class therefore violates the rule.
static void CheckCovergroupAssignStmt(
    const Stmt* s, const std::unordered_set<std::string_view>& cg_names,
    DiagEngine& diag) {
  if (!s) return;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->lhs->kind == ExprKind::kIdentifier &&
      cg_names.count(s->lhs->text)) {
    diag.Error(s->range.start,
               std::format("embedded covergroup '{}' shall only be assigned "
                           "inside the new() method of its class",
                           s->lhs->text));
  }
  for (const auto* sub : s->stmts) {
    CheckCovergroupAssignStmt(sub, cg_names, diag);
  }
  CheckCovergroupAssignStmt(s->then_branch, cg_names, diag);
  CheckCovergroupAssignStmt(s->else_branch, cg_names, diag);
  CheckCovergroupAssignStmt(s->body, cg_names, diag);
  CheckCovergroupAssignStmt(s->for_body, cg_names, diag);
  for (const auto& ci : s->case_items) {
    CheckCovergroupAssignStmt(ci.body, cg_names, diag);
  }
}

// §19.4: collects the names of all embedded covergroups declared in the class.
static std::unordered_set<std::string_view> CollectCovergroupNames(
    const ClassDecl* cls) {
  std::unordered_set<std::string_view> cg_names;
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kCovergroup && !m->name.empty()) {
      cg_names.insert(m->name);
    }
  }
  return cg_names;
}

// §19.4: checks every non-constructor method of the class for assignments to an
// embedded covergroup identifier, which are forbidden outside new().
static void CheckClassMethodsForCovergroupAssign(
    const ClassDecl* cls, const std::unordered_set<std::string_view>& cg_names,
    DiagEngine& diag) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
    // The constructor is the one place an embedded covergroup may be
    // instantiated, so assignments there are permitted.
    if (m->method->name == "new") continue;
    for (const auto* s : m->method->func_body_stmts) {
      CheckCovergroupAssignStmt(s, cg_names, diag);
    }
  }
}

void Elaborator::ValidateEmbeddedCovergroupAssign() {
  for (const auto* cls : unit_->classes) {
    std::unordered_set<std::string_view> cg_names = CollectCovergroupNames(cls);
    if (cg_names.empty()) continue;
    CheckClassMethodsForCovergroupAssign(cls, cg_names, diag_);
  }
}

// §19.4.1: a derived embedded covergroup, written `covergroup extends base ;`,
// inherits the covergroup named by `base`. It shall be an error to use the
// extends form when no covergroup of that name has previously been defined in a
// base class of the enclosing class. The search starts at the immediate base
// class and follows the inheritance chain upward; a covergroup defined in the
// derived class itself does not satisfy the requirement.
static bool BaseClassDefinesCovergroup(const ClassDecl* cls,
                                       std::string_view cg_name,
                                       const CompilationUnit* unit) {
  for (const ClassDecl* base = cls->base_class.empty()
                                   ? nullptr
                                   : FindClassDecl(cls->base_class, unit);
       base; base = base->base_class.empty()
                        ? nullptr
                        : FindClassDecl(base->base_class, unit)) {
    for (const auto* m : base->members) {
      if (m->kind == ClassMemberKind::kCovergroup && m->name == cg_name) {
        return true;
      }
    }
  }
  return false;
}

void Elaborator::ValidateDerivedCovergroupBase() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kCovergroup) continue;
      if (m->covergroup_extends_base.empty()) continue;
      if (!BaseClassDefinesCovergroup(cls, m->covergroup_extends_base, unit_)) {
        diag_.Error(
            m->loc,
            std::format("derived covergroup cannot extend '{}': no covergroup "
                        "of that name is defined in a base class",
                        m->covergroup_extends_base));
      }
    }
  }
}

void Elaborator::ValidateClassMethodBodies(const ModuleDecl* decl) {
  auto validate_class_methods = [&](const ClassDecl* cls) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      ValidateFunctionBody(m->method);
    }
  };
  for (const auto* cls : unit_->classes) {
    validate_class_methods(cls);
  }
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kClassDecl || !item->class_decl) continue;
    validate_class_methods(item->class_decl);
  }
}

static void ApplyAutoToClassMethods(const ClassDecl* cls) {
  if (!cls) return;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        !m->method->is_automatic && !m->method->is_static) {
      m->method->is_automatic = true;
    }

    if (m->kind == ClassMemberKind::kClassDecl && m->nested_class) {
      ApplyAutoToClassMethods(m->nested_class);
    }
  }
}

void Elaborator::ApplyClassMethodAutomaticDefault() {
  for (auto* cls : unit_->classes) ApplyAutoToClassMethods(cls);
  for (auto* mod : unit_->modules) {
    for (auto* item : mod->items) {
      if (item->kind == ModuleItemKind::kClassDecl) {
        ApplyAutoToClassMethods(item->class_decl);
      }
    }
  }
  for (auto* pkg : unit_->packages) {
    for (auto* item : pkg->items) {
      if (item->kind == ModuleItemKind::kClassDecl) {
        ApplyAutoToClassMethods(item->class_decl);
      }
    }
  }
}

static bool ExprRefsSuper(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == "super") return true;
  if (ExprRefsSuper(e->lhs) || ExprRefsSuper(e->rhs) ||
      ExprRefsSuper(e->base) || ExprRefsSuper(e->index) ||
      ExprRefsSuper(e->condition) || ExprRefsSuper(e->true_expr) ||
      ExprRefsSuper(e->false_expr) || ExprRefsSuper(e->with_expr)) {
    return true;
  }
  for (const auto* elem : e->elements)
    if (ExprRefsSuper(elem)) return true;
  for (const auto* arg : e->args)
    if (ExprRefsSuper(arg)) return true;
  return false;
}

static bool StmtRefsSuper(const Stmt* s) {
  if (!s) return false;
  if (ExprRefsSuper(s->lhs)) return true;
  if (ExprRefsSuper(s->rhs)) return true;
  if (ExprRefsSuper(s->expr)) return true;
  if (ExprRefsSuper(s->condition)) return true;
  for (auto* sub : s->stmts)
    if (StmtRefsSuper(sub)) return true;
  if (StmtRefsSuper(s->then_branch)) return true;
  if (StmtRefsSuper(s->else_branch)) return true;
  if (StmtRefsSuper(s->body)) return true;
  if (StmtRefsSuper(s->for_body)) return true;
  for (auto& ci : s->case_items)
    if (StmtRefsSuper(ci.body)) return true;
  return false;
}

// §8.15: in a class that does not extend another, no method body may reference
// 'super'. Reports the first offending method statement.
static void CheckNonDerivedClassMethodsForSuper(const ClassDecl* cls,
                                                DiagEngine& diag) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
    for (const auto* s : m->method->func_body_stmts) {
      if (StmtRefsSuper(s)) {
        diag.Error(m->method->loc,
                   "'super' shall only be used in a derived class");
        break;
      }
    }
  }
}

void Elaborator::ValidateSuperInNonDerivedClass() {
  for (const auto* cls : unit_->classes) {
    if (!cls->base_class.empty()) continue;
    CheckNonDerivedClassMethodsForSuper(cls, diag_);
  }
}

// §8.17: returns the class's own 'new' constructor method, or null if the
// class declares none.
static const ModuleItem* FindClassCtorMethod(const ClassDecl* cls) {
  if (!cls) return nullptr;
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      return m->method;
    }
  }
  return nullptr;
}

// §8.17: returns whether an expression tree references any identifier whose
// name appears in 'names'. Mirrors the traversal used for 'super' detection.
static bool ExprRefsAnyName(const Expr* e,
                            const std::unordered_set<std::string_view>& names) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && names.count(e->text)) return true;
  if (ExprRefsAnyName(e->lhs, names) || ExprRefsAnyName(e->rhs, names) ||
      ExprRefsAnyName(e->base, names) || ExprRefsAnyName(e->index, names) ||
      ExprRefsAnyName(e->condition, names) ||
      ExprRefsAnyName(e->true_expr, names) ||
      ExprRefsAnyName(e->false_expr, names) ||
      ExprRefsAnyName(e->with_expr, names)) {
    return true;
  }
  for (const auto* elem : e->elements)
    if (ExprRefsAnyName(elem, names)) return true;
  for (const auto* arg : e->args)
    if (ExprRefsAnyName(arg, names)) return true;
  return false;
}

// §8.17: returns whether a constructor's argument list uses the 'default'
// keyword.
static bool CtorArgListUsesDefault(const ModuleItem* ctor) {
  if (!ctor) return false;
  for (const auto& arg : ctor->func_args) {
    if (arg.is_default) return true;
  }
  return false;
}

// §8.17: 'default' may be passed as the sole argument to super.new() only when
// the enclosing constructor's own argument list used the 'default' keyword.
// This handles the case where it did not, flagging any such super.new() call.
static void CheckDefaultArgInSuperNewCall(const ModuleItem* ctor,
                                          DiagEngine& diag) {
  for (const auto* s : ctor->func_body_stmts) {
    if (!IsSuperNewCall(s)) continue;
    const auto& call_args = s->expr->args;
    if (call_args.size() == 1 && call_args[0] &&
        call_args[0]->kind == ExprKind::kIdentifier &&
        call_args[0]->text == "default") {
      diag.Error(s->range.start,
                 "'default' may be passed to super.new() only when the "
                 "constructor argument list uses the 'default' keyword");
    }
  }
}

// §8.17: because 'default' expands to the superclass constructor arguments, an
// explicit argument in the subclass constructor shall not share a name with any
// superclass constructor argument.
static void CheckDefaultCtorArgNameConflicts(const ModuleItem* ctor,
                                             const ModuleItem* base_ctor,
                                             DiagEngine& diag) {
  std::unordered_set<std::string_view> base_arg_names;
  for (const auto& a : base_ctor->func_args) {
    if (!a.name.empty()) base_arg_names.insert(a.name);
  }
  for (const auto& a : ctor->func_args) {
    if (a.is_default || a.name.empty()) continue;
    if (base_arg_names.count(a.name)) {
      diag.Error(ctor->loc,
                 std::format("constructor argument '{}' shall not share a "
                             "name with a superclass constructor argument "
                             "when 'default' is used",
                             a.name));
    }
  }
}

// §8.17: 'default' shall not be used when a superclass constructor argument's
// default value refers to a local member of the superclass.
static void CheckDefaultCtorArgRefsBaseLocal(const ClassDecl* base,
                                             const ModuleItem* ctor,
                                             const ModuleItem* base_ctor,
                                             DiagEngine& diag) {
  std::unordered_set<std::string_view> base_locals;
  for (const auto* m : base->members) {
    if (m->is_local && !m->name.empty()) base_locals.insert(m->name);
  }
  if (base_locals.empty()) return;
  for (const auto& a : base_ctor->func_args) {
    if (a.default_value && ExprRefsAnyName(a.default_value, base_locals)) {
      diag.Error(ctor->loc,
                 "'default' shall not be used when a superclass constructor "
                 "argument default value refers to a local member");
      break;
    }
  }
}

// §8.17: enforces the rules governing the 'default' keyword in a subclass
// constructor argument list and in an explicit super.new() call.
void Elaborator::ValidateOneClassDefaultKeyword(const ClassDecl* cls) {
  const ModuleItem* ctor = FindClassCtorMethod(cls);

  bool ctor_has_default = CtorArgListUsesDefault(ctor);

  // §8.17: 'default' expands to the superclass constructor's arguments, so the
  // class shall extend another class for the expansion to have a source.
  if (ctor_has_default && cls->base_class.empty()) {
    diag_.Error(ctor->loc,
                "'default' in a constructor argument list requires the class "
                "to extend a superclass");
  }

  // §8.17: when the extends specifier uses 'default' and the subclass also
  // defines its own constructor, that constructor's argument list shall repeat
  // the 'default' keyword.
  if (cls->extends_has_default && ctor && !ctor_has_default) {
    diag_.Error(ctor->loc,
                "constructor argument list shall contain 'default' when the "
                "extends specifier uses the 'default' keyword");
  }

  // §8.17: 'default' may be passed as the sole argument to super.new() only
  // when the constructor's own argument list used the 'default' keyword.
  if (ctor && !ctor_has_default) {
    CheckDefaultArgInSuperNewCall(ctor, diag_);
  }

  if (!ctor_has_default || cls->base_class.empty()) return;

  const ClassDecl* base = FindClassDecl(cls->base_class, unit_);
  const ModuleItem* base_ctor = FindClassCtorMethod(base);
  if (!base_ctor) return;

  CheckDefaultCtorArgNameConflicts(ctor, base_ctor, diag_);
  CheckDefaultCtorArgRefsBaseLocal(base, ctor, base_ctor, diag_);
}

void Elaborator::ValidateChainingConstructors() {
  for (const auto* cls : unit_->classes) {
    ValidateOneClassChainingCtor(cls);
    ValidateOneClassDefaultKeyword(cls);
  }
}

}  // namespace delta
