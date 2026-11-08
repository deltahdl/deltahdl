#include <format>
#include <optional>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/class_method_reads.h"
#include "elaborator/covergroup_context.h"
#include "elaborator/covergroup_rules.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/std_package.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

void ElaboratorClassRules::ValidateFinalClassExtension() {
  auto check = [&](const ClassDecl* cls) {
    if (cls->base_class.empty()) return;

    const std::optional<StdPackageMember> kStd =
        StdPackageMemberNamed(cls->base_class);
    if (kStd && StdClassIsFinal(*kStd)) {
      diag_.Error(cls->range.start, "cannot extend a class declared ':final'",
                  Subclause("8.13"));
      return;
    }
    const auto* base = FindBaseClass(cls, unit_);
    if (base && base->is_final) {
      diag_.Error(cls->range.start, "cannot extend a class declared ':final'",
                  Subclause("8.13"));
    }
  };
  for (const auto* cls : AllClassDecls(unit_)) {
    check(cls);
  }
}

void ElaboratorClassRules::ValidateWeakReferenceMembers() {
  auto check_member = [&](const ClassMember* m) {
    if (m->kind != ClassMemberKind::kProperty) return;
    if (m->data_type.kind != DataTypeKind::kNamed) return;
    if (m->data_type.type_name != "weak_reference") return;
    if (m->data_type.type_params.empty()) return;
    const auto& tp = m->data_type.type_params[0];
    if (!WeakRefTypeParamNamesClass(tp, typedefs_, class_names_)) {
      diag_.Error(m->loc,
                  "weak_reference needs a class type as its type parameter",
                  Subclause("8.30.1"));
    }
  };
  for (const auto* cls : AllClassDecls(unit_)) {
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

static bool StmtSubtreeHasSuperNew(const Stmt* s) {
  if (!s) return false;
  if (IsSuperNewCall(s)) return true;
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtSubtreeHasSuperNew(sub);
  });
  return found;
}

static bool ConstructorHasGuardedSuperNew(const Stmt* s) {
  if (!s) return false;
  if (s->kind == StmtKind::kBlock) {
    for (const auto* sub : s->stmts) {
      if (ConstructorHasGuardedSuperNew(sub)) return true;
    }
    return false;
  }
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtSubtreeHasSuperNew(sub);
  });
  return found;
}

static const ClassMember* FindClassConstructor(const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      return m;
    }
  }
  return nullptr;
}

static bool ReportSequentialSuperNew(const ModuleItem* method,
                                     DiagEngine& diag) {
  bool executed = false;
  for (const Stmt* s : method->func_body_stmts) {
    if (IsSuperNewCall(s)) {
      if (executed) {
        diag.Error(s->range.start,
                   "super.new() does not open the constructor, and no "
                   "executable statement may come before it",
                   Subclause("8.17"));
      }
      return true;
    }
    executed = executed || s->kind != StmtKind::kVarDecl;
  }
  return false;
}

static void ReportGuardedSuperNew(const ModuleItem* method, DiagEngine& diag) {
  for (const auto* s : method->func_body_stmts) {
    if (ConstructorHasGuardedSuperNew(s)) {
      diag.Error(s->range.start,
                 "super.new() does not open the constructor, and no "
                 "executable statement may come before it",
                 Subclause("8.17"));
      return;
    }
  }
}

void ElaboratorClassRules::ValidateOneClassChainingCtor(const ClassDecl* cls) {
  if (cls->base_class.empty()) return;
  const ClassMember* ctor = FindClassConstructor(cls);
  if (!ctor || !ctor->method) return;
  const ModuleItem* body = MethodBody(ctor->method);
  bool has_super_new = ReportSequentialSuperNew(body, diag_);
  if (!has_super_new) ReportGuardedSuperNew(body, diag_);
  if (has_super_new &&
      (!cls->extends_args.empty() || cls->extends_has_default)) {
    diag_.Error(body->loc,
                "constructor calls super.new() although the extends "
                "specifier already supplies the superclass constructor's "
                "arguments",
                Subclause("8.17"));
  }
}

static std::string_view AssignedCovergroupName(
    const Expr* lhs, const std::unordered_set<std::string_view>& cg_names) {
  if (lhs == nullptr) return {};
  if (lhs->kind == ExprKind::kIdentifier && cg_names.count(lhs->text)) {
    return lhs->text;
  }
  if (lhs->kind == ExprKind::kMemberAccess && !lhs->is_scope_resolution &&
      lhs->lhs != nullptr && lhs->lhs->kind == ExprKind::kIdentifier &&
      lhs->lhs->text == "this" && lhs->rhs != nullptr &&
      lhs->rhs->kind == ExprKind::kIdentifier &&
      cg_names.count(lhs->rhs->text)) {
    return lhs->rhs->text;
  }
  return {};
}

static void CheckCovergroupAssignStmt(
    const Stmt* s, const std::unordered_set<std::string_view>& cg_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    std::string_view cg = AssignedCovergroupName(s->lhs, cg_names);
    if (!cg.empty()) {
      diag.Error(s->range.start,
                 std::format("embedded covergroup '{}' shall only be assigned "
                             "inside the new() method of its class",
                             cg),
                 Subclause("19.4"));
    }
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckCovergroupAssignStmt(sub, cg_names, diag);
  });
}

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

static void CheckClassMethodsForCovergroupAssign(
    const ClassDecl* cls, const std::unordered_set<std::string_view>& cg_names,
    DiagEngine& diag) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
    if (m->method->name == "new") continue;
    for (const auto* s : m->method->func_body_stmts) {
      CheckCovergroupAssignStmt(s, cg_names, diag);
    }
  }
}

static std::vector<std::pair<const ClassDecl*, const std::vector<ModuleItem*>*>>
ClassesWithScopes(const CompilationUnit* unit) {
  std::vector<std::pair<const ClassDecl*, const std::vector<ModuleItem*>*>>
      classes;
  classes.reserve(unit->classes.size());
  for (const auto* cls : unit->classes)
    classes.emplace_back(cls, &unit->cu_items);
  auto add_scoped = [&](const std::vector<ModuleItem*>& items) {
    for (const auto* item : items) {
      if (item->kind == ModuleItemKind::kClassDecl) {
        classes.emplace_back(item->class_decl, &items);
      }
    }
  };
  for (const auto* scopes :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const auto* scope : *scopes) add_scoped(scope->items);
  }
  for (const auto* pkg : unit->packages) add_scoped(pkg->items);
  return classes;
}

void ElaboratorClassRules::ValidateEmbeddedCovergroupAssign() {
  for (const auto& [cls, scope_items] : ClassesWithScopes(unit_)) {
    std::unordered_set<std::string_view> cg_names = CollectCovergroupNames(cls);
    if (cg_names.empty()) continue;
    CheckClassMethodsForCovergroupAssign(cls, cg_names, diag_);
  }
}

void ElaboratorClassRules::ValidateEmbeddedCovergroupRules() {
  UnitDeclaredNames names(unit_);
  CovergroupDeclared unit_declared = [&names](std::string_view name) {
    return names.Declares(name);
  };
  for (const auto& [cls, scope_items] : ClassesWithScopes(unit_)) {
    ValidateEmbeddedCovergroups(cls, *scope_items, unit_, unit_declared, diag_);
  }
}

static bool BaseClassDefinesCovergroup(const ClassDecl* cls,
                                       std::string_view cg_name,
                                       const CompilationUnit* unit) {
  for (const ClassDecl* base = FindBaseClass(cls, unit); base;
       base = FindBaseClass(base, unit)) {
    for (const auto* m : base->members) {
      if (m->kind == ClassMemberKind::kCovergroup && m->name == cg_name) {
        return true;
      }
    }
  }
  return false;
}

void ElaboratorClassRules::ValidateDerivedCovergroupBase() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kCovergroup) continue;
      if (m->covergroup_extends_base.empty()) continue;
      if (!BaseClassDefinesCovergroup(cls, m->covergroup_extends_base, unit_)) {
        diag_.Error(
            m->loc,
            std::format("derived covergroup cannot extend '{}': no covergroup "
                        "of that name is defined in a base class",
                        m->covergroup_extends_base),
            Subclause("19.4.1"));
      }
    }
  }
}

void Elaborator::ValidateClassMethodBodies(const ModuleDecl* decl) {
  auto validate_class_methods = [&](const ClassDecl* cls) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      ValidateFunctionBody(m->method, true);
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

void ElaboratorClassRules::ApplyClassMethodAutomaticDefault() {
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
  for (const Expr* child :
       {e->lhs, e->rhs, e->base, e->index, e->condition, e->true_expr,
        e->false_expr, e->with_expr, e->stream_range}) {
    if (ExprRefsSuper(child)) return true;
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
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtRefsSuper(sub);
  });
  return found;
}

static void CheckNonDerivedClassMethodsForSuper(const ClassDecl* cls,
                                                DiagEngine& diag) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
    const ModuleItem* body = MethodBody(m->method);
    for (const auto* s : body->func_body_stmts) {
      if (StmtRefsSuper(s)) {
        diag.Error(body->loc, "'super' shall only be used in a derived class",
                   Subclause("8.15"));
        break;
      }
    }
  }
}

static std::string_view ParamKindIn(const ClassDecl* cls,
                                    std::string_view name) {
  for (const auto& p : cls->params) {
    if (p.first != name || cls->type_param_names.count(p.first)) continue;
    return cls->localparam_port_names.count(p.first) ? "local value parameter"
                                                     : "value parameter";
  }
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty && m->is_param &&
        m->name == name) {
      return "local value parameter";
    }
  }
  return {};
}

static const ClassDecl* BaseOf(const ClassDecl* cls,
                               const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  return FindBaseClass(cls, unit);
}

static std::string_view SuperParamKind(const ClassDecl* cls,
                                       std::string_view name,
                                       const CompilationUnit* unit) {
  std::unordered_set<const ClassDecl*> seen;
  for (const ClassDecl* base = BaseOf(cls, unit);
       base && seen.insert(base).second; base = BaseOf(base, unit)) {
    std::string_view kind = ParamKindIn(base, name);
    if (!kind.empty()) return kind;
  }
  return {};
}

static void CheckConstExprForSuperParam(const Expr* e, const ClassDecl* cls,
                                        const CompilationUnit* unit,
                                        DiagEngine& diag) {
  if (!e) return;
  const Expr* access = e;
  if (access->kind == ExprKind::kMemberAccess && !access->is_scope_resolution &&
      access->lhs && access->lhs->kind == ExprKind::kIdentifier &&
      access->lhs->text == "super" && access->rhs &&
      access->rhs->kind == ExprKind::kIdentifier) {
    std::string_view name = access->rhs->text;
    std::string_view kind = SuperParamKind(cls, name, unit);
    if (!kind.empty()) {
      diag.Error(access->range.start,
                 std::format("expression using 'super' to access base class {} "
                             "'{}' is not a constant expression",
                             kind, name),
                 Subclause("8.15"));
      return;
    }
  }
  CheckConstExprForSuperParam(e->lhs, cls, unit, diag);
  CheckConstExprForSuperParam(e->rhs, cls, unit, diag);
  CheckConstExprForSuperParam(e->base, cls, unit, diag);
  CheckConstExprForSuperParam(e->index, cls, unit, diag);
  CheckConstExprForSuperParam(e->index_end, cls, unit, diag);
  CheckConstExprForSuperParam(e->repeat_count, cls, unit, diag);
  CheckConstExprForSuperParam(e->condition, cls, unit, diag);
  CheckConstExprForSuperParam(e->true_expr, cls, unit, diag);
  CheckConstExprForSuperParam(e->false_expr, cls, unit, diag);
  CheckConstExprForSuperParam(e->with_expr, cls, unit, diag);
  CheckConstExprForSuperParam(e->stream_range, cls, unit, diag);
  for (const auto* elem : e->elements)
    CheckConstExprForSuperParam(elem, cls, unit, diag);
  for (const auto* arg : e->args)
    CheckConstExprForSuperParam(arg, cls, unit, diag);
}

static void CheckStmtConstantContexts(const Stmt* s, const ClassDecl* cls,
                                      const CompilationUnit* unit,
                                      DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl) {
    if (s->var_is_static) {
      CheckConstExprForSuperParam(s->var_init, cls, unit, diag);
    }
    for (const auto* dim : s->var_unpacked_dims) {
      CheckConstExprForSuperParam(dim, cls, unit, diag);
    }
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckStmtConstantContexts(sub, cls, unit, diag);
  });
}

static void CheckSuperParamInConstantExpr(const ClassDecl* cls,
                                          const CompilationUnit* unit,
                                          DiagEngine& diag) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
    for (const auto* s : MethodBody(m->method)->func_body_stmts) {
      CheckStmtConstantContexts(s, cls, unit, diag);
    }
  }
}

void ElaboratorClassRules::ValidateSuperRules() {
  for (const auto* cls : AllClassDecls(unit_)) {
    if (cls->base_class.empty()) {
      CheckNonDerivedClassMethodsForSuper(cls, diag_);
    } else {
      CheckSuperParamInConstantExpr(cls, unit_, diag_);
    }
  }
}

static const ModuleItem* FindClassCtorMethod(const ClassDecl* cls) {
  if (!cls) return nullptr;
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      return MethodBody(m->method);
    }
  }
  return nullptr;
}

static bool ExprRefsAnyName(const Expr* e,
                            const std::unordered_set<std::string_view>& names) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && names.count(e->text)) return true;
  for (const Expr* child :
       {e->lhs, e->rhs, e->base, e->index, e->condition, e->true_expr,
        e->false_expr, e->with_expr, e->stream_range}) {
    if (ExprRefsAnyName(child, names)) return true;
  }
  for (const auto* elem : e->elements)
    if (ExprRefsAnyName(elem, names)) return true;
  for (const auto* arg : e->args)
    if (ExprRefsAnyName(arg, names)) return true;
  return false;
}

static bool CtorArgListUsesDefault(const ModuleItem* ctor) {
  if (!ctor) return false;
  for (const auto& arg : ctor->func_args) {
    if (arg.is_default) return true;
  }
  return false;
}

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
                 "constructor argument list uses the 'default' keyword",
                 Subclause("8.17"));
    }
  }
}

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
                             a.name),
                 Subclause("8.17"));
    }
  }
}

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
                 "'default' is unavailable because a superclass constructor "
                 "argument's default value refers to a local member",
                 Subclause("8.17"));
      break;
    }
  }
}

void ElaboratorClassRules::ValidateOneClassDefaultKeyword(
    const ClassDecl* cls) {
  const ModuleItem* ctor = FindClassCtorMethod(cls);

  bool ctor_has_default = CtorArgListUsesDefault(ctor);

  if (ctor_has_default && cls->base_class.empty()) {
    diag_.Error(ctor->loc,
                "'default' in a constructor argument list requires the class "
                "to extend a superclass",
                Subclause("8.17"));
  }

  if (cls->extends_has_default && ctor && !ctor_has_default) {
    diag_.Error(ctor->loc,
                "the extends specifier uses 'default', so the constructor's "
                "argument list has to repeat 'default'",
                Subclause("8.17"));
  }

  if (ctor && !ctor_has_default) {
    CheckDefaultArgInSuperNewCall(ctor, diag_);
  }

  if (!ctor_has_default || cls->base_class.empty()) return;

  const ClassDecl* base = FindBaseClass(cls, unit_);
  const ModuleItem* base_ctor = FindClassCtorMethod(base);
  if (!base_ctor) return;

  CheckDefaultCtorArgNameConflicts(ctor, base_ctor, diag_);
  CheckDefaultCtorArgRefsBaseLocal(base, ctor, base_ctor, diag_);
}

void ElaboratorClassRules::ValidateChainingConstructors() {
  for (const auto* cls : AllClassDecls(unit_)) {
    ValidateOneClassChainingCtor(cls);
    ValidateOneClassDefaultKeyword(cls);
  }
}

}  // namespace delta
