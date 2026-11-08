#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/block_name_space.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

void ValidateRefLifetime(const ModuleItem* func, DiagEngine& diag);
void ValidateConstRefWriteProtection(const ModuleItem* func, DiagEngine& diag);

static void CheckNoReturnInFork(const Stmt* s, bool in_production_code_block,
                                DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kReturn) {
    if (!in_production_code_block) {
      diag.Error(s->range.start,
                 "return statement is not allowed inside a fork-join block",
                 Subclause("9.3.2"));
    }
    return;
  }
  bool in_production =
      in_production_code_block || s->kind == StmtKind::kRandsequence;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckNoReturnInFork(sub, in_production, diag);
  });
}

static void CheckExprForRefArgs(
    const Expr* e, const std::unordered_set<std::string_view>& ref_names,
    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kIdentifier && ref_names.count(e->text)) {
    diag.Error(e->range.start,
               std::format("ref argument '{}' cannot be used inside a "
                           "fork-join_any or fork-join_none block",
                           e->text),
               Subclause("9.3.2"));
    return;
  }
  CheckExprForRefArgs(e->lhs, ref_names, diag);
  CheckExprForRefArgs(e->rhs, ref_names, diag);
  CheckExprForRefArgs(e->condition, ref_names, diag);
  CheckExprForRefArgs(e->true_expr, ref_names, diag);
  CheckExprForRefArgs(e->false_expr, ref_names, diag);
  CheckExprForRefArgs(e->base, ref_names, diag);
  CheckExprForRefArgs(e->index, ref_names, diag);
  CheckExprForRefArgs(e->index_end, ref_names, diag);
  CheckExprForRefArgs(e->with_expr, ref_names, diag);
  CheckExprForRefArgs(e->stream_range, ref_names, diag);
  CheckExprForRefArgs(e->repeat_count, ref_names, diag);
  for (auto* arg : e->args) CheckExprForRefArgs(arg, ref_names, diag);
  for (auto* elem : e->elements) CheckExprForRefArgs(elem, ref_names, diag);
}

static void CheckStmtExprsForRefArgs(
    const Stmt* s, const std::unordered_set<std::string_view>& ref_names,
    bool is_fork_block_item, DiagEngine& diag) {
  if (!is_fork_block_item || s->kind != StmtKind::kVarDecl)
    CheckExprForRefArgs(s->var_init, ref_names, diag);
  CheckExprForRefArgs(s->expr, ref_names, diag);
  CheckExprForRefArgs(s->lhs, ref_names, diag);
  CheckExprForRefArgs(s->rhs, ref_names, diag);
  CheckExprForRefArgs(s->delay, ref_names, diag);
  CheckExprForRefArgs(s->cycle_delay, ref_names, diag);
  CheckExprForRefArgs(s->condition, ref_names, diag);
  CheckExprForRefArgs(s->for_cond, ref_names, diag);
  CheckExprForRefArgs(s->assert_expr, ref_names, diag);
  CheckExprForRefArgs(s->repeat_event_count, ref_names, diag);
  for (auto* dim : s->var_unpacked_dims)
    CheckExprForRefArgs(dim, ref_names, diag);
  for (auto& ev : s->events) {
    CheckExprForRefArgs(ev.signal, ref_names, diag);
    CheckExprForRefArgs(ev.iff_condition, ref_names, diag);
  }
  for (auto& ci : s->case_items)
    for (auto* p : ci.patterns) CheckExprForRefArgs(p, ref_names, diag);
  for (auto& ri : s->randcase_items)
    CheckExprForRefArgs(ri.first, ref_names, diag);
  for (auto* we : s->wait_order_events)
    CheckExprForRefArgs(we, ref_names, diag);
}

static void CheckStmtForRefArgs(
    const Stmt* s, const std::unordered_set<std::string_view>& ref_names,
    bool is_fork_block_item, DiagEngine& diag) {
  if (!s) return;
  CheckStmtExprsForRefArgs(s, ref_names, is_fork_block_item, diag);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckStmtForRefArgs(sub, ref_names, false, diag);
  });
}

static void CheckRefArgsInForkBlocks(
    const Stmt* s, const std::unordered_set<std::string_view>& ref_names,
    bool enclosed, DiagEngine& diag) {
  if (!s) return;
  bool is_async_fork =
      s->kind == StmtKind::kFork && (s->join_kind == TokenKind::kKwJoinAny ||
                                     s->join_kind == TokenKind::kKwJoinNone);
  if (is_async_fork && !enclosed) {
    for (auto* fs : s->fork_stmts) {
      bool is_block_item = (fs->kind == StmtKind::kVarDecl);
      CheckStmtForRefArgs(fs, ref_names, is_block_item, diag);
    }
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckRefArgsInForkBlocks(sub, ref_names, enclosed || is_async_fork, diag);
  });
}

static bool HasIntraAssignmentTiming(const Stmt* s) {
  if (s->kind != StmtKind::kBlockingAssign &&
      s->kind != StmtKind::kNonblockingAssign)
    return false;
  return s->delay != nullptr || !s->events.empty();
}

static void CheckFuncBodyTimeControl(const Stmt* s, DiagEngine& diag) {
  if (s->kind == StmtKind::kDelay || s->kind == StmtKind::kCycleDelay ||
      s->kind == StmtKind::kEventControl ||
      s->kind == StmtKind::kTimingControl || s->kind == StmtKind::kWait ||
      s->kind == StmtKind::kWaitFork || s->kind == StmtKind::kWaitOrder ||
      s->kind == StmtKind::kExpect || HasIntraAssignmentTiming(s)) {
    diag.Error(s->range.start,
               "time-controlling statement is not allowed inside a function",
               Subclause("13.4"));
  }
}

static void CheckFuncBodyVarDecl(const Stmt* s, std::string_view func_name,
                                 DiagEngine& diag) {
  if (s->kind != StmtKind::kVarDecl) return;
  if (!func_name.empty() && s->var_name == func_name) {
    diag.Error(s->range.start,
               std::format("declaration of '{}' conflicts with function name",
                           func_name),
               Subclause("13.4.1"));
  }
}

struct FunctionBodyScope {
  bool is_void = false;
  std::string_view func_name;
  const std::unordered_set<std::string>& task_names;
  bool in_production_code_block = false;
  bool in_fork = false;
};

static void CheckFuncBodyStmtSelf(const Stmt* s, const FunctionBodyScope& scope,
                                  DiagEngine& diag) {
  if (s->kind == StmtKind::kReturn && s->expr && scope.is_void &&
      !scope.in_production_code_block) {
    diag.Error(s->range.start, "void function returns a value",
               Subclause("13.4.1"));
  }
  if (s->kind == StmtKind::kFork && s->join_kind != TokenKind::kKwJoinNone) {
    diag.Error(s->range.start,
               "only fork/join_none is permitted inside a function",
               Subclause("13.4"));
  }

  CheckFuncBodyTimeControl(s, diag);

  if (scope.task_names.contains(EnabledSubroutineName(s))) {
    diag.Error(s->range.start, "function cannot enable a task",
               Subclause("13.4"));
  }

  CheckFuncBodyVarDecl(s, scope.func_name, diag);

  if (s->kind == StmtKind::kAssign && s->lhs &&
      s->lhs->kind == ExprKind::kSelect) {
    diag.Error(s->range.start,
               "bit-select or part-select in procedural assign LHS",
               Subclause("10.6.1"));
  }

  if (s->kind == StmtKind::kFork && !scope.in_fork) {
    for (auto* sub : s->fork_stmts)
      CheckNoReturnInFork(sub, scope.in_production_code_block, diag);
  }
}

static void CheckFuncBodyStmt(const Stmt* s, const FunctionBodyScope& scope,
                              DiagEngine& diag) {
  if (!s) return;
  CheckFuncBodyStmtSelf(s, scope, diag);

  if (s->kind == StmtKind::kFork && s->join_kind == TokenKind::kKwJoinNone)
    return;

  FunctionBodyScope inner = scope;
  if (s->kind == StmtKind::kRandsequence) inner.in_production_code_block = true;
  if (s->kind == StmtKind::kFork) inner.in_fork = true;
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckFuncBodyStmt(sub, inner, diag); });
}

static bool ExprRefsAutoVar(
    const Expr* e, const std::unordered_set<std::string_view>& auto_vars);

static bool AnyChildExprRefsAutoVar(
    const Expr* e, const std::unordered_set<std::string_view>& auto_vars) {
  const Expr* const kChildren[] = {
      e->lhs,       e->rhs,          e->base,        e->index,
      e->index_end, e->condition,    e->true_expr,   e->false_expr,
      e->with_expr, e->stream_range, e->repeat_count};
  for (const Expr* child : kChildren)
    if (ExprRefsAutoVar(child, auto_vars)) return true;
  for (auto* a : e->args)
    if (ExprRefsAutoVar(a, auto_vars)) return true;
  for (auto* el : e->elements)
    if (ExprRefsAutoVar(el, auto_vars)) return true;
  return false;
}

static bool ExprRefsAutoVar(
    const Expr* e, const std::unordered_set<std::string_view>& auto_vars) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && !e->text.empty() &&
      auto_vars.count(e->text) != 0)
    return true;
  return AnyChildExprRefsAutoVar(e, auto_vars);
}

struct AutoVarRule {
  std::string_view variable;
  Subclause subclause;
};

constexpr AutoVarRule kAutomaticTaskVar{"automatic task variable",
                                        Subclause("13.3.2")};
constexpr AutoVarRule kAutomaticVarInStaticScope{"automatic variable",
                                                 Subclause("6.21")};
constexpr AutoVarRule kAutomaticFunctionVar{"automatic variable",
                                            Subclause("10.4.2")};

struct HandleNames {
  const NameSet& class_names;
  const TypedefMap& typedefs;
};

static bool IsHandleType(const DataType& type, const HandleNames& names) {
  const DataType* t = &type;
  while (t->kind == DataTypeKind::kNamed &&
         names.class_names.count(t->type_name) == 0) {
    auto it = names.typedefs.find(t->type_name);
    if (it == names.typedefs.end()) return false;
    t = &it->second;
  }
  return t->kind == DataTypeKind::kVirtualInterface ||
         t->kind == DataTypeKind::kNamed;
}

static bool NbaNameIsAutomatic(std::string_view name, bool through_member,
                               const BodyDeclScopes& scopes,
                               const HandleNames& class_names) {
  const BodyDeclScopes::Decl* decl = scopes.Find(name);
  if (decl == nullptr || !decl->automatic) return false;
  return !through_member || !IsHandleType(*decl->type, class_names);
}

static bool NbaTargetWritesAutomatic(const Expr* e, bool through_member,
                                     const BodyDeclScopes& scopes,
                                     const HandleNames& class_names) {
  if (e->kind == ExprKind::kConcatenation ||
      e->kind == ExprKind::kAssignmentPattern) {
    for (const Expr* el : e->elements)
      if (NbaTargetWritesAutomatic(el, false, scopes, class_names)) return true;
    return false;
  }
  if (e->kind == ExprKind::kSelect)
    return NbaTargetWritesAutomatic(e->base, through_member, scopes,
                                    class_names);
  if (e->kind == ExprKind::kMemberAccess)
    return NbaTargetWritesAutomatic(e->lhs, true, scopes, class_names);
  return e->kind == ExprKind::kIdentifier &&
         NbaNameIsAutomatic(e->text, through_member, scopes, class_names);
}

struct NbaAutoReport {
  const AutoVarRule& rule;
  const HandleNames& class_names;
  DiagEngine& diag;
};

static void CheckNbaAutomaticTargets(const std::vector<FunctionArg>& formals,
                                     const std::vector<Stmt*>& body,
                                     bool default_auto,
                                     const NbaAutoReport& report) {
  const AutoVarRule& rule = report.rule;
  const HandleNames& class_names = report.class_names;
  DiagEngine& diag = report.diag;
  BodyDeclScopes scopes(default_auto);
  for (const auto& arg : formals) scopes.DeclareFormal(arg);
  for (const Stmt* s : body) {
    scopes.Walk(s, [&](const Stmt* st) {
      if (st->kind != StmtKind::kNonblockingAssign) return;
      if (!NbaTargetWritesAutomatic(st->lhs, false, scopes, class_names))
        return;
      diag.Error(st->range.start,
                 std::format("{} in nonblocking assignment", rule.variable),
                 rule.subclause);
    });
  }
}

static void CheckNbaEventControlForAutoVar(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    const AutoVarRule& rule, DiagEngine& diag) {
  bool in_event_control = ExprRefsAutoVar(s->repeat_event_count, auto_vars);
  for (const auto& ev : s->events) {
    if (ExprRefsAutoVar(ev.signal, auto_vars) ||
        ExprRefsAutoVar(ev.iff_condition, auto_vars)) {
      in_event_control = true;
    }
  }
  if (in_event_control) {
    diag.Error(s->range.start,
               std::format("{} in intra-assignment event control of "
                           "nonblocking assignment",
                           rule.variable),
               rule.subclause);
  }
}

static bool IsTracingSystemTask(std::string_view name) {
  if (name == "$dumpvars") return true;
  name.remove_prefix(name.starts_with("$f") ? 2 : 1);
  return name == "monitor" || name == "monitorb" || name == "monitoro" ||
         name == "monitorh";
}

static void CheckTaskBodyMonitorTrace(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    const AutoVarRule& rule, DiagEngine& diag) {
  if (s->kind != StmtKind::kExprStmt || !s->expr ||
      s->expr->kind != ExprKind::kSystemCall ||
      !IsTracingSystemTask(s->expr->callee))
    return;
  for (auto* a : s->expr->args) {
    if (ExprRefsAutoVar(a, auto_vars)) {
      diag.Error(s->range.start,
                 std::format("{} traced by system task", rule.variable),
                 rule.subclause);
      break;
    }
  }
}

static void CheckTaskBodyContAssign(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    const AutoVarRule& rule, DiagEngine& diag) {
  if (s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign) {
    auto name = ExprIdent(s->lhs);
    if ((!name.empty() && auto_vars.count(name) != 0) ||
        ExprRefsAutoVar(s->rhs, auto_vars)) {
      diag.Error(
          s->range.start,
          std::format("{} in procedural continuous assignment", rule.variable),
          rule.subclause);
    }
  }
  if (s->kind == StmtKind::kAssign && s->lhs &&
      s->lhs->kind == ExprKind::kSelect) {
    diag.Error(s->range.start,
               "bit-select or part-select in procedural assign LHS",
               Subclause("10.6.1"));
  }
}

struct TaskBodyScope {
  const std::unordered_set<std::string_view>& auto_vars;
  const AutoVarRule& rule;
  bool in_production_code_block = false;
  bool in_fork = false;
};

static void CheckTaskBodyStmtSelf(const Stmt* s, const TaskBodyScope& scope,
                                  DiagEngine& diag) {
  if (s->kind == StmtKind::kReturn && s->expr &&
      !scope.in_production_code_block) {
    diag.Error(s->range.start, "task returns a value", Subclause("13.3"));
  }

  if (s->kind == StmtKind::kNonblockingAssign)
    CheckNbaEventControlForAutoVar(s, scope.auto_vars, scope.rule, diag);
  CheckTaskBodyMonitorTrace(s, scope.auto_vars, scope.rule, diag);
  CheckTaskBodyContAssign(s, scope.auto_vars, scope.rule, diag);

  if (s->kind == StmtKind::kFork && !scope.in_fork) {
    for (auto* sub : s->fork_stmts)
      CheckNoReturnInFork(sub, scope.in_production_code_block, diag);
  }
}

static void CheckTaskBodyStmt(const Stmt* s, const TaskBodyScope& scope,
                              DiagEngine& diag) {
  if (!s) return;
  CheckTaskBodyStmtSelf(s, scope, diag);
  TaskBodyScope inner = scope;
  if (s->kind == StmtKind::kRandsequence) inner.in_production_code_block = true;
  if (s->kind == StmtKind::kFork) inner.in_fork = true;
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckTaskBodyStmt(sub, inner, diag); });
}

static void CollectAutoVarNames(const Stmt* s, bool task_is_auto,
                                std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    if ((task_is_auto && !s->var_is_static) ||
        (!task_is_auto && s->var_is_automatic)) {
      out.insert(s->var_name);
    }
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CollectAutoVarNames(sub, task_is_auto, out);
  });
}

static void ValidateFunctionArgDecls(
    const ModuleItem* item, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names, DiagEngine& diag) {
  for (const auto& arg : item->func_args) {
    if (arg.data_type.kind == DataTypeKind::kNamed &&
        arg.data_type.type_name == "weak_reference" &&
        !arg.data_type.type_params.empty()) {
      const auto& tp = arg.data_type.type_params[0];
      if (!WeakRefTypeParamNamesClass(tp, typedefs, class_names)) {
        diag.Error(item->loc,
                   "weak_reference needs a class type as its type parameter",
                   Subclause("8.30.1"));
      }
    }
    if (arg.default_value && !item->is_ansi_ports) {
      diag.Error(item->loc,
                 std::format("default argument values are only allowed with "
                             "ANSI-style port declarations for '{}'",
                             arg.name),
                 Subclause("13.5.3"));
    }
  }
}

static void ValidateRefArgsInForkBlocks(const ModuleItem* item,
                                        DiagEngine& diag) {
  std::unordered_set<std::string_view> ref_names;
  for (const auto& arg : item->func_args) {
    if (arg.direction == Direction::kRef && !arg.is_ref_static) {
      ref_names.insert(arg.name);
    }
  }
  if (!ref_names.empty()) {
    for (auto* s : item->func_body_stmts)
      CheckRefArgsInForkBlocks(s, ref_names, false, diag);
  }
}

static void ValidateTaskBody(const ModuleItem* item, bool is_auto,
                             const HandleNames& class_names, DiagEngine& diag) {
  std::unordered_set<std::string_view> auto_vars;
  if (is_auto) {
    for (const auto& arg : item->func_args) {
      auto_vars.insert(arg.name);
    }
  }
  for (auto* s : item->func_body_stmts) {
    CollectAutoVarNames(s, is_auto, auto_vars);
  }
  const AutoVarRule& rule =
      is_auto ? kAutomaticTaskVar : kAutomaticVarInStaticScope;
  CheckNbaAutomaticTargets(item->func_args, item->func_body_stmts, is_auto,
                           {rule, class_names, diag});
  TaskBodyScope scope{.auto_vars = auto_vars, .rule = rule};
  for (auto* s : item->func_body_stmts) {
    CheckTaskBodyStmt(s, scope, diag);
  }
}

void Elaborator::ValidateFunctionBody(const ModuleItem* item,
                                      bool is_class_method) {
  ValidateRefLifetime(item, diag_);

  ValidateConstRefWriteProtection(item, diag_);

  ValidateFunctionArgDecls(item, typedefs_, class_names_, diag_);

  ValidateRefArgsInForkBlocks(item, diag_);

  std::unordered_set<std::string_view> formals;
  for (const auto& arg : item->func_args) formals.insert(arg.name);
  CheckBlockNameSpace(item->func_body_stmts, std::move(formals), diag_);
  for (auto* s : item->func_body_stmts) CheckNestedBlockNameSpaces(s, diag_);

  bool is_auto = item->is_automatic || is_class_method;
  if (item->kind == ModuleItemKind::kTaskDecl) {
    ValidateTaskBody(item, is_auto, {class_names_, typedefs_}, diag_);
    return;
  }
  if (item->kind != ModuleItemKind::kFunctionDecl) return;
  const HandleNames kHandles{class_names_, typedefs_};
  CheckNbaAutomaticTargets(item->func_args, item->func_body_stmts, is_auto,
                           {kAutomaticFunctionVar, kHandles, diag_});
  bool is_void = (item->return_type.kind == DataTypeKind::kVoid);
  const std::unordered_set<std::string> kTasks = ReachableTaskNames();
  FunctionBodyScope scope{
      .is_void = is_void, .func_name = item->name, .task_names = kTasks};
  for (auto* s : item->func_body_stmts) {
    CheckFuncBodyStmt(s, scope, diag_);
  }
}

static void CheckAutoVarWritesInProc(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign) {
    auto name = ExprIdent(s->lhs);
    if (!name.empty() && auto_vars.count(name) != 0) {
      diag.Error(s->range.start,
                 "automatic block variable in procedural continuous assignment",
                 Subclause("6.21"));
    }
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckAutoVarWritesInProc(sub, auto_vars, diag);
  });
}

static void ReportImplicitlyStaticInit(const Stmt* s, DiagEngine& diag) {
  if (s == nullptr || s->kind == StmtKind::kRandsequence) return;
  if (s->kind == StmtKind::kVarDecl && s->var_init != nullptr &&
      !s->var_is_static && !s->var_is_automatic && !s->var_is_param) {
    diag.Error(s->range.start,
               std::format("variable '{}' declared with an initializer in a "
                           "static block, task or function must be declared "
                           "static or automatic",
                           s->var_name),
               Subclause("6.21"));
  }
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { ReportImplicitlyStaticInit(sub, diag); });
}

static void ReportImplicitlyStaticInitsOfItem(const ModuleItem* item,
                                              bool scope_is_automatic,
                                              DiagEngine& diag) {
  if (IsProceduralItemKind(item->kind)) {
    if (!scope_is_automatic) ReportImplicitlyStaticInit(item->body, diag);
    return;
  }
  if (item->kind != ModuleItemKind::kTaskDecl &&
      item->kind != ModuleItemKind::kFunctionDecl)
    return;
  if (!item->method_class.empty()) return;
  if (item->is_automatic || (scope_is_automatic && !item->is_static)) return;
  for (const auto* s : item->func_body_stmts)
    ReportImplicitlyStaticInit(s, diag);
}

static void ValidateAutomaticVarRulesOfItems(
    const std::vector<ModuleItem*>& items, bool module_is_automatic,
    const HandleNames& class_names, DiagEngine& diag);

static void ValidateAutomaticVarRulesOfGenerate(const ModuleItem* item,
                                                bool module_is_automatic,
                                                const HandleNames& class_names,
                                                DiagEngine& diag) {
  switch (item->kind) {
    case ModuleItemKind::kGenerateIf:
      ValidateAutomaticVarRulesOfItems(item->gen_body, module_is_automatic,
                                       class_names, diag);
      if (item->gen_else != nullptr)
        ValidateAutomaticVarRulesOfGenerate(item->gen_else, module_is_automatic,
                                            class_names, diag);
      return;
    case ModuleItemKind::kGenerateFor:
      ValidateAutomaticVarRulesOfItems(item->gen_body, module_is_automatic,
                                       class_names, diag);
      return;
    case ModuleItemKind::kGenerateCase:
      for (const auto& ci : item->gen_case_items)
        ValidateAutomaticVarRulesOfItems(ci.body, module_is_automatic,
                                         class_names, diag);
      return;
    default:
      return;
  }
}

static void ValidateAutomaticVarRulesOfItems(
    const std::vector<ModuleItem*>& items, bool module_is_automatic,
    const HandleNames& class_names, DiagEngine& diag) {
  for (const auto* item : items) {
    ReportImplicitlyStaticInitsOfItem(item, module_is_automatic, diag);
    ValidateAutomaticVarRulesOfGenerate(item, module_is_automatic, class_names,
                                        diag);
    bool is_proc = IsProceduralItemKind(item->kind);
    if (!is_proc || !item->body) continue;
    CheckNbaAutomaticTargets({}, {item->body}, false,
                             {kAutomaticVarInStaticScope, class_names, diag});
    std::unordered_set<std::string_view> auto_vars;
    CollectAutoVarNames(item->body, false, auto_vars);
    if (auto_vars.empty()) continue;
    CheckAutoVarWritesInProc(item->body, auto_vars, diag);
  }
}

void Elaborator::ValidateAutomaticVarProcWrites(const ModuleDecl* decl) {
  ValidateAutomaticVarRulesOfItems(decl->items, decl->is_automatic,
                                   {class_names_, typedefs_}, diag_);
}

void ReportPackageSubroutineStaticInits(const PackageDecl* pkg,
                                        DiagEngine& diag) {
  for (const auto* item : pkg->items) {
    if (IsProceduralItemKind(item->kind)) continue;
    ReportImplicitlyStaticInitsOfItem(item, pkg->is_automatic, diag);
  }
}

}  // namespace delta
