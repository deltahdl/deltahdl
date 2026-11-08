#include <cstddef>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

static void CollectHierPathComponents(const Expr* e,
                                      std::vector<std::string_view>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kIdentifier) {
    out.push_back(e->text);
    return;
  }
  if (e->kind == ExprKind::kMemberAccess) {
    CollectHierPathComponents(e->lhs, out);
    CollectHierPathComponents(e->rhs, out);
  }
}

struct ProgramScopes {
  std::unordered_set<std::string_view> names;
  std::unordered_set<std::string_view> locals;
  const CompilationUnit* unit = nullptr;
  const ModuleDecl* scope = nullptr;
  bool every_reference = false;

  void Shadow(std::string_view name) {
    names.erase(name);
    locals.insert(name);
  }
};

static const ModuleDecl* FindDesignElement(const CompilationUnit* unit,
                                           std::string_view name) {
  for (const auto* decls :
       {&unit->modules, &unit->programs, &unit->interfaces}) {
    for (const auto* d : *decls)
      if (!d->is_extern && d->name == name) return d;
  }
  return nullptr;
}

static const ModuleDecl* FindInstanceElement(const ModuleDecl* decl,
                                             std::string_view inst_name,
                                             const CompilationUnit* unit) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kModuleInst &&
        item->inst_name == inst_name)
      return FindDesignElement(unit, item->inst_module);
  }
  return nullptr;
}

static bool PathReachesProgram(const Expr* e, const ProgramScopes& scopes) {
  std::vector<std::string_view> path;
  CollectHierPathComponents(e, path);
  if (path.size() < 2) return false;
  const ModuleDecl* decl = nullptr;
  if (scopes.scope != nullptr)
    decl = FindInstanceElement(scopes.scope, path[0], scopes.unit);
  if (decl == nullptr) decl = FindDesignElement(scopes.unit, path[0]);
  for (size_t i = 1; decl != nullptr; ++i) {
    if (decl->decl_kind == ModuleDeclKind::kProgram) return true;
    if (i + 1 >= path.size()) return false;
    decl = FindInstanceElement(decl, path[i], scopes.unit);
  }
  return false;
}

static bool PathNamesProgram(const Expr* e, const ProgramScopes& scopes) {
  auto leftmost = HierRefLeftmost(e);
  return !leftmost.empty() && scopes.locals.count(leftmost) == 0 &&
         (scopes.names.count(leftmost) != 0 ||
          (scopes.unit != nullptr && PathReachesProgram(e, scopes)));
}

static bool ExprRefersToProgram(const Expr* e, const ProgramScopes& scopes) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess && PathNamesProgram(e, scopes))
    return true;
  bool skip_callee = e->kind == ExprKind::kCall && !scopes.every_reference;
  return AnyExprChild(e, [&](const Expr* c) {
    return (!skip_callee || c != e->lhs) && ExprRefersToProgram(c, scopes);
  });
}

static void ReportProgramSignalRef(SourceLoc loc, DiagEngine& diag) {
  diag.Error(loc,
             "hierarchical reference to program signal from outside the "
             "program is not permitted",
             Subclause("24.3"));
}

static const Expr* SubroutineEnableOfStmt(const Stmt* s) {
  if (const Expr* call = SubroutineCallOfStmt(s)) return call;
  if (s->kind == StmtKind::kExprStmt && s->expr != nullptr &&
      s->expr->kind == ExprKind::kMemberAccess)
    return s->expr;
  return nullptr;
}

static void WalkStmtsForProgramRef(const Stmt* s, ProgramScopes scopes,
                                   DiagEngine& diag) {
  if (!s) return;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (sub != nullptr && sub->kind == StmtKind::kVarDecl)
      scopes.Shadow(sub->var_name);
  });
  const Expr* call =
      scopes.every_reference ? nullptr : SubroutineEnableOfStmt(s);
  ForEachChildExpr(s, [&](Expr* const& e) {
    if ((call == nullptr || e != s->expr) && ExprRefersToProgram(e, scopes))
      ReportProgramSignalRef(s->range.start, diag);
  });
  if (call != nullptr && AnyExprChild(call, [&](const Expr* arg) {
        return arg != call->lhs && ExprRefersToProgram(arg, scopes);
      }))
    ReportProgramSignalRef(s->range.start, diag);
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtsForProgramRef(sub, scopes, diag); });
}

static void WalkSubroutineBodyForProgramRef(const ModuleItem* item,
                                            ProgramScopes scopes,
                                            DiagEngine& diag) {
  for (const auto& arg : item->func_args) scopes.Shadow(arg.name);
  for (const auto* s : item->func_body_stmts) {
    if (s != nullptr && s->kind == StmtKind::kVarDecl)
      scopes.Shadow(s->var_name);
  }
  for (const auto* s : item->func_body_stmts) {
    WalkStmtsForProgramRef(s, scopes, diag);
  }
}

static void CheckContAssignForProgramRef(const ModuleItem* item,
                                         const ProgramScopes& scopes,
                                         DiagEngine& diag) {
  if (ExprRefersToProgram(item->assign_lhs, scopes))
    ReportProgramSignalRef(item->loc, diag);
  if (ExprRefersToProgram(item->assign_rhs, scopes))
    ReportProgramSignalRef(item->loc, diag);
}

static void CheckClassMethodsForProgramRef(const ClassDecl* cls,
                                           const ProgramScopes& scopes,
                                           DiagEngine& diag) {
  if (cls == nullptr) return;
  for (const auto* member : cls->members) {
    if (member == nullptr) continue;
    if (member->method != nullptr)
      WalkSubroutineBodyForProgramRef(member->method, scopes, diag);
    if (member->kind == ClassMemberKind::kClassDecl)
      CheckClassMethodsForProgramRef(member->nested_class, scopes, diag);
  }
}

static bool UnitDeclaresNamedProgram(const CompilationUnit* unit) {
  for (const auto* p : unit->programs)
    if (!p->name.empty() && !p->is_extern) return true;
  return false;
}

void Elaborator::ValidateHierRefIntoProgram(const ModuleDecl* decl) {
  if (decl->decl_kind == ModuleDeclKind::kProgram) return;
  if (program_inst_names_.empty() && !UnitDeclaresNamedProgram(unit_)) return;
  const ProgramScopes kScopes{program_inst_names_, {}, unit_, decl};
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign)
      CheckContAssignForProgramRef(item, kScopes, diag_);
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body)
      WalkStmtsForProgramRef(item->body, kScopes, diag_);
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl)
      WalkSubroutineBodyForProgramRef(item, kScopes, diag_);
    CheckClassMethodsForProgramRef(item->class_decl, kScopes, diag_);
  }
}

static void CheckScopeItemsForAnonymousProgramHierRefs(
    const std::vector<ModuleItem*>& items, const ProgramScopes& scopes,
    DiagEngine& diag) {
  for (const auto* item : items) {
    if (!item->from_anonymous_program) continue;
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      WalkSubroutineBodyForProgramRef(item, scopes, diag);
    }
    CheckClassMethodsForProgramRef(item->class_decl, scopes, diag);
  }
}

void Elaborator::ValidateAnonymousProgramHierRefs() {
  ProgramScopes scopes;
  scopes.unit = unit_;
  scopes.every_reference = true;
  for (const auto* p : unit_->programs) {
    if (!p->name.empty() && !p->is_extern) scopes.names.insert(p->name);
  }
  if (scopes.names.empty()) return;
  CheckScopeItemsForAnonymousProgramHierRefs(unit_->cu_items, scopes, diag_);
  for (const auto* pkg : unit_->packages) {
    CheckScopeItemsForAnonymousProgramHierRefs(pkg->items, scopes, diag_);
  }
}

static bool ExprRefersToAutomatic(
    const Expr* e, const std::unordered_set<std::string_view>& auto_names) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) {
    std::vector<std::string_view> components;
    CollectHierPathComponents(e, components);
    for (size_t i = 0; i + 1 < components.size(); ++i) {
      if (auto_names.count(components[i])) return true;
    }
  }
  if (ExprRefersToAutomatic(e->lhs, auto_names)) return true;
  if (ExprRefersToAutomatic(e->rhs, auto_names)) return true;
  if (ExprRefersToAutomatic(e->base, auto_names)) return true;
  for (auto* elem : e->elements) {
    if (ExprRefersToAutomatic(elem, auto_names)) return true;
  }
  return false;
}

struct AutoSubroutineRule {
  const std::unordered_set<std::string_view>& names;
  std::string_view message;
  Subclause subclause;
};

static std::unordered_set<std::string_view> AutoSubroutineNames(
    const ModuleDecl* decl, ModuleItemKind kind) {
  std::unordered_set<std::string_view> names;
  for (const auto* item : decl->items) {
    if (item->kind == kind && item->is_automatic) names.insert(item->name);
  }
  return names;
}

static void WalkStmtsForAutoRef(const Stmt* s, const AutoSubroutineRule& rule,
                                DiagEngine& diag) {
  if (!s) return;
  if (s->lhs && ExprRefersToAutomatic(s->lhs, rule.names))
    diag.Error(s->range.start, std::string(rule.message), rule.subclause);
  if (s->rhs && ExprRefersToAutomatic(s->rhs, rule.names))
    diag.Error(s->range.start, std::string(rule.message), rule.subclause);
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtsForAutoRef(sub, rule, diag); });
}

static void CheckHierRefToAutomatic(const ModuleDecl* decl,
                                    const AutoSubroutineRule& rule,
                                    DiagEngine& diag) {
  if (rule.names.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      if (ExprRefersToAutomatic(item->assign_lhs, rule.names))
        diag.Error(item->loc, std::string(rule.message), rule.subclause);
      if (ExprRefersToAutomatic(item->assign_rhs, rule.names))
        diag.Error(item->loc, std::string(rule.message), rule.subclause);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) WalkStmtsForAutoRef(item->body, rule, diag);
  }
}

void Elaborator::ValidateHierRefToAutomatic(const ModuleDecl* decl) {
  if (auto_task_func_names_.empty()) return;
  auto tasks = AutoSubroutineNames(decl, ModuleItemKind::kTaskDecl);
  CheckHierRefToAutomatic(
      decl,
      {tasks,
       "hierarchical reference to object in automatic task is not permitted",
       Subclause("13.3.1")},
      diag_);
  auto funcs = AutoSubroutineNames(decl, ModuleItemKind::kFunctionDecl);
  CheckHierRefToAutomatic(
      decl,
      {funcs,
       "hierarchical reference to object in automatic function is not "
       "permitted",
       Subclause("13.4.2")},
      diag_);
}

static bool IsProgramSubroutineCallExpr(const Expr* e,
                                        const ProgramScopes& scopes) {
  if (!e || e->kind != ExprKind::kCall) return false;
  const Expr* callee = e->lhs;
  return callee != nullptr && callee->kind == ExprKind::kMemberAccess &&
         PathNamesProgram(callee, scopes);
}

static void WalkExprForProgramCall(const Expr* e, const ProgramScopes& scopes,
                                   DiagEngine& diag, SourceLoc loc) {
  if (!e) return;
  if (IsProgramSubroutineCallExpr(e, scopes)) {
    diag.Error(loc,
               "calling a program subroutine from within a design module is "
               "not permitted",
               Subclause("24.5"));
  }
  WalkExprForProgramCall(e->lhs, scopes, diag, loc);
  WalkExprForProgramCall(e->rhs, scopes, diag, loc);
  WalkExprForProgramCall(e->condition, scopes, diag, loc);
  WalkExprForProgramCall(e->true_expr, scopes, diag, loc);
  WalkExprForProgramCall(e->false_expr, scopes, diag, loc);
  WalkExprForProgramCall(e->base, scopes, diag, loc);
  WalkExprForProgramCall(e->index, scopes, diag, loc);
  WalkExprForProgramCall(e->index_end, scopes, diag, loc);
  WalkExprForProgramCall(e->with_expr, scopes, diag, loc);
  WalkExprForProgramCall(e->stream_range, scopes, diag, loc);
  WalkExprForProgramCall(e->repeat_count, scopes, diag, loc);
  for (auto* arg : e->args) WalkExprForProgramCall(arg, scopes, diag, loc);
  for (auto* elem : e->elements)
    WalkExprForProgramCall(elem, scopes, diag, loc);
}

static void WalkStmtForProgramCall(const Stmt* s, ProgramScopes scopes,
                                   DiagEngine& diag) {
  if (!s) return;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (sub != nullptr && sub->kind == StmtKind::kVarDecl)
      scopes.Shadow(sub->var_name);
  });
  auto loc = s->range.start;
  if (const Expr* call = SubroutineEnableOfStmt(s);
      call != nullptr && call->kind == ExprKind::kMemberAccess &&
      PathNamesProgram(call, scopes))
    diag.Error(loc,
               "calling a program subroutine from within a design module is "
               "not permitted",
               Subclause("24.5"));
  WalkExprForProgramCall(s->lhs, scopes, diag, loc);
  WalkExprForProgramCall(s->rhs, scopes, diag, loc);
  WalkExprForProgramCall(s->expr, scopes, diag, loc);
  WalkExprForProgramCall(s->condition, scopes, diag, loc);
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtForProgramCall(sub, scopes, diag); });
}

static void WalkSubroutineBodyForProgramCall(const ModuleItem* item,
                                             ProgramScopes scopes,
                                             DiagEngine& diag) {
  for (const auto& arg : item->func_args) scopes.Shadow(arg.name);
  for (const auto* s : item->func_body_stmts) {
    if (s != nullptr && s->kind == StmtKind::kVarDecl)
      scopes.Shadow(s->var_name);
  }
  for (const auto* s : item->func_body_stmts) {
    WalkStmtForProgramCall(s, scopes, diag);
  }
}

static void ReportProgramWideSpaceAccess(SourceLoc loc, DiagEngine& diag) {
  diag.Error(loc,
             "an identifier declared inside an anonymous program cannot be "
             "referenced outside any program block",
             Subclause("24.6"));
}

static void WalkStmtForProgramWideSpaceAccess(
    const Stmt* s, std::unordered_set<std::string_view> names,
    DiagEngine& diag) {
  if (!s) return;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (sub != nullptr && sub->kind == StmtKind::kVarDecl) {
      names.erase(sub->var_name);
    }
  });
  ForEachChildExpr(s, [&](Expr* const& e) {
    if (ExprMentionsAny(e, names))
      ReportProgramWideSpaceAccess(s->range.start, diag);
  });
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtForProgramWideSpaceAccess(sub, names, diag);
  });
}

static void CheckItemForProgramWideSpaceAccess(
    const ModuleItem* item, const std::unordered_set<std::string_view>& names,
    DiagEngine& diag);

static void CheckClassMethodsForProgramWideSpaceAccess(
    const ClassDecl* cls, const std::unordered_set<std::string_view>& names,
    DiagEngine& diag) {
  if (cls == nullptr) return;
  for (const auto* member : cls->members) {
    if (member == nullptr) continue;
    if (member->method != nullptr)
      CheckItemForProgramWideSpaceAccess(member->method, names, diag);
    if (member->kind == ClassMemberKind::kClassDecl)
      CheckClassMethodsForProgramWideSpaceAccess(member->nested_class, names,
                                                 diag);
  }
}

static void CheckItemForProgramWideSpaceAccess(
    const ModuleItem* item, const std::unordered_set<std::string_view>& names,
    DiagEngine& diag) {
  for (bool mentions : {names.count(item->data_type.type_name) != 0,
                        ExprMentionsAny(item->init_expr, names),
                        ExprMentionsAny(item->assign_lhs, names),
                        ExprMentionsAny(item->assign_rhs, names)}) {
    if (mentions) ReportProgramWideSpaceAccess(item->loc, diag);
  }
  if (IsProceduralItemKind(item->kind))
    WalkStmtForProgramWideSpaceAccess(item->body, names, diag);
  std::unordered_set<std::string_view> body_names = names;
  for (const auto& arg : item->func_args) body_names.erase(arg.name);
  for (const auto* s : item->func_body_stmts) {
    if (s != nullptr && s->kind == StmtKind::kVarDecl) {
      body_names.erase(s->var_name);
    }
  }
  for (const auto* s : item->func_body_stmts)
    WalkStmtForProgramWideSpaceAccess(s, body_names, diag);
  CheckClassMethodsForProgramWideSpaceAccess(item->class_decl, names, diag);
}

void Elaborator::ValidateProgramWideSpaceAccess(const ModuleDecl* decl) {
  if (anonymous_program_names_.empty()) return;
  if (decl->decl_kind == ModuleDeclKind::kProgram) return;
  std::unordered_set<std::string_view> names = anonymous_program_names_;
  for (const auto* item : decl->items) names.erase(item->name);
  for (const auto* item : decl->items) {
    CheckItemForProgramWideSpaceAccess(item, names, diag_);
  }
}

static void CheckScopeItemsForProgramWideSpaceAccess(
    const std::vector<ModuleItem*>& items,
    const std::unordered_set<std::string_view>& names, DiagEngine& diag) {
  for (const auto* item : items) {
    if (item->from_anonymous_program) continue;
    CheckItemForProgramWideSpaceAccess(item, names, diag);
  }
}

void Elaborator::ValidateProgramWideSpaceAccessInPackageAndCuScopes() {
  if (anonymous_program_names_.empty()) return;
  CheckScopeItemsForProgramWideSpaceAccess(unit_->cu_items,
                                           anonymous_program_names_, diag_);
  for (const auto* pkg : unit_->packages) {
    CheckScopeItemsForProgramWideSpaceAccess(pkg->items,
                                             anonymous_program_names_, diag_);
  }
  for (const auto* cls : unit_->classes) {
    CheckClassMethodsForProgramWideSpaceAccess(cls, anonymous_program_names_,
                                               diag_);
  }
}

static void CheckClassMethodsForProgramCall(const ClassDecl* cls,
                                            const ProgramScopes& scopes,
                                            DiagEngine& diag) {
  if (cls == nullptr) return;
  for (const auto* member : cls->members) {
    if (member == nullptr) continue;
    if (member->method != nullptr)
      WalkSubroutineBodyForProgramCall(member->method, scopes, diag);
    if (member->kind == ClassMemberKind::kClassDecl)
      CheckClassMethodsForProgramCall(member->nested_class, scopes, diag);
  }
}

void Elaborator::ValidateProgramSubroutineCall(const ModuleDecl* decl) {
  if (decl->decl_kind == ModuleDeclKind::kProgram) return;
  if (program_inst_names_.empty() && !UnitDeclaresNamedProgram(unit_)) return;
  const ProgramScopes kScopes{program_inst_names_, {}, unit_, decl};
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForProgramCall(item->assign_lhs, kScopes, diag_, item->loc);
      WalkExprForProgramCall(item->assign_rhs, kScopes, diag_, item->loc);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body)
      WalkStmtForProgramCall(item->body, kScopes, diag_);
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl)
      WalkSubroutineBodyForProgramCall(item, kScopes, diag_);
    CheckClassMethodsForProgramCall(item->class_decl, kScopes, diag_);
  }
}

}  // namespace delta
