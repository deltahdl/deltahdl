#include <algorithm>
#include <cstddef>
#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/assertion_rules.h"
#include "elaborator/attached_call_target.h"
#include "elaborator/checker_actual_rules.h"
#include "elaborator/checker_procedure_rules.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/net_data_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

using SequenceDeclMap = std::unordered_map<std::string_view, const ModuleItem*>;

static void CheckSequenceActualArgCount(Stmt* s, const Expr* call,
                                        const ModuleItem* decl,
                                        DiagEngine& diag) {
  if (!call->arg_names.empty()) return;
  for (const auto* a : call->args) {
    if (!a) return;
  }
  size_t actuals = call->args.size();
  size_t total = decl->prop_formals.size();
  size_t required = 0;
  for (size_t i = 0; i < total; ++i) {
    bool has_default = i < decl->prop_formal_has_default.size() &&
                       decl->prop_formal_has_default[i];
    if (!has_default) ++required;
  }
  if (actuals < required) {
    diag.Error(s->range.start,
               "sequence instance omits an actual argument for a formal that "
               "has no default",
               Subclause("16.8"));
  } else if (actuals > total) {
    diag.Error(s->range.start,
               "sequence instance provides more actual arguments than the "
               "sequence has formal arguments",
               Subclause("16.8"));
  }
}

struct SequenceEventCtx {
  const std::unordered_set<std::string_view>& seq_names;
  const SequenceDeclMap& seq_decls;
  const std::unordered_set<std::string_view>& automatic_names;
  DiagEngine& diag;
};

static void MarkSequenceEvent(Stmt* s, EventExpr& ev,
                              const SequenceEventCtx& ctx) {
  if (!ev.signal) return;
  std::string_view name;
  bool has_args = false;
  if (ev.signal->kind == ExprKind::kIdentifier) {
    name = ev.signal->text;
  } else if (ev.signal->kind == ExprKind::kCall) {
    name = ev.signal->callee;
    has_args = !ev.signal->args.empty();
  }
  if (name.empty() || ctx.seq_names.count(name) == 0) return;
  ev.is_sequence_event = true;

  if (has_args && std::ranges::any_of(ev.signal->args, [&](const Expr* a) {
        return ExprMentionsAny(a, ctx.automatic_names);
      })) {
    ctx.diag.Error(s->range.start,
                   "sequence event arguments shall not reference "
                   "automatic variables",
                   Subclause("9.4.2.4"));
  }
  if (ev.signal->kind == ExprKind::kCall) {
    auto it = ctx.seq_decls.find(name);
    if (it != ctx.seq_decls.end()) {
      CheckSequenceActualArgCount(s, ev.signal, it->second, ctx.diag);
    }
  }
}

static void WalkStmtsForSequenceEvents(Stmt* s, const SequenceEventCtx& ctx) {
  if (!s) return;
  if (s->kind == StmtKind::kEventControl) {
    for (auto& ev : s->events) MarkSequenceEvent(s, ev, ctx);
  }
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtsForSequenceEvents(sub, ctx); });
}

static void CollectAutomaticVarNames(
    const Stmt* s, bool automatic_by_default,
    std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl &&
      (s->var_is_automatic || (automatic_by_default && !s->var_is_static))) {
    out.insert(s->var_name);
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CollectAutomaticVarNames(sub, automatic_by_default, out);
  });
}

std::unordered_set<std::string_view> CollectItemAutomaticVarNames(
    const ModuleItem* item) {
  bool routine_is_automatic = (item->kind == ModuleItemKind::kTaskDecl ||
                               item->kind == ModuleItemKind::kFunctionDecl) &&
                              item->is_automatic;
  std::unordered_set<std::string_view> auto_vars;
  if (routine_is_automatic) {
    for (const auto& fa : item->func_args) auto_vars.insert(fa.name);
  }
  CollectAutomaticVarNames(item->body, routine_is_automatic, auto_vars);
  for (const auto* st : item->func_body_stmts) {
    CollectAutomaticVarNames(st, routine_is_automatic, auto_vars);
  }
  return auto_vars;
}

static void WalkItemForSequenceEvents(
    const ModuleItem* item,
    const std::unordered_set<std::string_view>& seq_names,
    const SequenceDeclMap& seq_decls, DiagEngine& diag) {
  if (item->kind != ModuleItemKind::kTaskDecl &&
      !IsProceduralItemKind(item->kind)) {
    return;
  }
  const std::unordered_set<std::string_view> kAutomaticNames =
      CollectItemAutomaticVarNames(item);
  std::vector<Stmt*> bodies(item->func_body_stmts.begin(),
                            item->func_body_stmts.end());
  bodies.push_back(const_cast<Stmt*>(item->body));
  const SequenceEventCtx kCtx{seq_names, seq_decls, kAutomaticNames, diag};
  for (Stmt* s : bodies) WalkStmtsForSequenceEvents(s, kCtx);
}

static void MarkSequenceClockEvents(
    std::vector<EventExpr>& clock,
    const std::unordered_set<std::string_view>& seq_names) {
  for (EventExpr& ev : clock) {
    if (ev.signal != nullptr && ev.signal->kind == ExprKind::kIdentifier &&
        seq_names.count(ev.signal->text) != 0) {
      ev.is_sequence_event = true;
    }
  }
}

void Elaborator::ValidateSequenceEventArgs(const ModuleDecl* decl,
                                           RtlirModule* mod) {
  ValidateAssertionRules(decl, property_registry_, diag_);
  const ScopeMap kParams = BuildParamScope(mod);
  ValidateAssertionExprRules(ModuleInUnit{*decl, *unit_}, mod, kParams,
                             property_registry_, diag_);
  ValidateAssertionBoundRules(decl, kParams, diag_);
  ValidateAssertionContextRules(decl, mod, property_registry_, diag_);
  ValidateLocalVariableFlow(decl, diag_);
  ValidateCheckerFormalDefaults(decl, diag_);
  const TypeShapeTables kShapeTables{typedefs_, td_array_dims_, class_names_};
  ValidateCheckerInterfaceFormals(decl, unit_, kShapeTables, diag_);
  ValidateCheckerEnclosingRefs(decl, kShapeTables, func_decls_, diag_);
  if (sequence_names_.empty()) return;
  SequenceDeclMap seq_decls;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) {
      seq_decls[item->name] = item;
    }
  }
  for (const auto* item : decl->items) {
    WalkItemForSequenceEvents(item, sequence_names_, seq_decls, diag_);
  }
  for (RtlirProcess& proc : mod->processes) {
    MarkSequenceClockEvents(proc.sensitivity, sequence_names_);
    if (proc.is_concurrent_clocked) {
      MarkSequenceClockEvents(proc.body->assert_clock, sequence_names_);
    }
  }
}

static bool IsSingleSubroutineCall(const Stmt* action) {
  if (!action) return true;
  if (action->kind == StmtKind::kNull) return true;
  return SubroutineCallOfStmt(action) != nullptr;
}

static bool ContainsPostponedIllegalStmt(const Stmt* s) {
  if (!s) return false;
  switch (s->kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
    case StmtKind::kAssign:
    case StmtKind::kDeassign:
    case StmtKind::kForce:
    case StmtKind::kRelease:
    case StmtKind::kEventTrigger:
    case StmtKind::kNbEventTrigger:
    case StmtKind::kDelay:
    case StmtKind::kEventControl:
    case StmtKind::kWait:
    case StmtKind::kCycleDelay:
      return true;
    default:
      break;
  }
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = ContainsPostponedIllegalStmt(sub);
  });
  return found;
}

static bool CalleeBodyHasPostponedIllegal(const ModuleItem* callee) {
  if (!callee) return false;
  if (callee->body && ContainsPostponedIllegalStmt(callee->body)) return true;
  for (auto* s : callee->func_body_stmts) {
    if (ContainsPostponedIllegalStmt(s)) return true;
  }
  return false;
}

using DeferredSubroutineMap =
    std::unordered_map<std::string_view, const ModuleItem*>;

static void CheckFinalDeferredCallee(const Stmt* action,
                                     const DeferredSubroutineMap& subs,
                                     DiagEngine& diag) {
  const Expr* call = SubroutineCallOfStmt(action);
  if (call == nullptr || call->kind != ExprKind::kCall) return;
  auto it = subs.find(call->callee);
  if (it == subs.end()) return;
  if (CalleeBodyHasPostponedIllegal(it->second)) {
    diag.Warning(action->range.start,
                 std::format("final deferred assertion calls '{}', whose body "
                             "contains statements not legally callable in the "
                             "Postponed region (§4.4.2.9)",
                             call->callee),
                 Subclause("16.4"));
  }
}

static void CheckDeferredRefActual(
    const Expr* a, const FunctionArg& formal,
    const std::unordered_set<std::string_view>& auto_vars, DiagEngine& diag) {
  if (!a) return;
  if (a->kind == ExprKind::kMemberAccess) {
    diag.Error(a->range.start,
               std::format("cannot pass dynamic variable as actual for "
                           "ref{} formal '{}' in deferred-assertion call",
                           formal.is_const ? " const" : "", formal.name),
               Subclause("16.4"));
    return;
  }
  if (a->kind == ExprKind::kIdentifier &&
      auto_vars.find(a->text) != auto_vars.end()) {
    diag.Error(a->range.start,
               std::format("cannot pass automatic variable as actual "
                           "for ref{} formal '{}' in deferred-assertion call",
                           formal.is_const ? " const" : "", formal.name),
               Subclause("16.4"));
  }
}

static void CheckDeferredCallRefArgs(
    const Stmt* action, const DeferredSubroutineMap& subs,
    const std::unordered_set<std::string_view>& auto_vars, DiagEngine& diag) {
  const Expr* call = SubroutineCallOfStmt(action);
  if (call == nullptr || call->kind != ExprKind::kCall) return;
  auto it = subs.find(call->callee);
  if (it == subs.end()) return;
  const auto& formals = it->second->func_args;
  const auto& actuals = call->args;
  size_t n = std::min(formals.size(), actuals.size());
  for (size_t i = 0; i < n; ++i) {
    if (formals[i].direction != Direction::kRef) continue;
    CheckDeferredRefActual(actuals[i], formals[i], auto_vars, diag);
  }
}

static void CheckDeferredActionStmt(
    const Stmt* s, const DeferredSubroutineMap& subs,
    const std::unordered_set<std::string_view>& auto_vars, DiagEngine& diag) {
  if (!s->is_deferred) return;
  if (s->kind != StmtKind::kAssertImmediate &&
      s->kind != StmtKind::kAssumeImmediate &&
      s->kind != StmtKind::kCoverImmediate) {
    return;
  }
  if (s->assert_pass_stmt && !IsSingleSubroutineCall(s->assert_pass_stmt)) {
    diag.Error(s->assert_pass_stmt->range.start,
               "deferred assertion pass action shall be a single "
               "subroutine call",
               Subclause("16.4"));
  }
  if (s->assert_fail_stmt && !IsSingleSubroutineCall(s->assert_fail_stmt)) {
    diag.Error(s->assert_fail_stmt->range.start,
               "deferred assertion fail action shall be a single "
               "subroutine call",
               Subclause("16.4"));
  }

  if (s->is_final_deferred) {
    CheckFinalDeferredCallee(s->assert_pass_stmt, subs, diag);
    CheckFinalDeferredCallee(s->assert_fail_stmt, subs, diag);
  }

  CheckDeferredCallRefArgs(s->assert_pass_stmt, subs, auto_vars, diag);
  CheckDeferredCallRefArgs(s->assert_fail_stmt, subs, auto_vars, diag);
}

void Elaborator::WalkStmtsForDeferredActions(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars) {
  if (!s) return;
  CheckDeferredActionStmt(s, deferred_subroutine_map_, auto_vars, diag_);
  ForEachChildStmt(s, [this, &auto_vars](Stmt* const& sub) {
    WalkStmtsForDeferredActions(sub, auto_vars);
  });
}

void Elaborator::ValidateDeferredAssertionActions(const ModuleDecl* decl) {
  deferred_subroutine_map_.clear();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      deferred_subroutine_map_[item->name] = item;
    }
  }
  for (const auto* item : decl->items) {
    if (!item->body && item->func_body_stmts.empty()) continue;
    std::unordered_set<std::string_view> auto_vars =
        CollectItemAutomaticVarNames(item);
    WalkStmtsForDeferredActions(item->body, auto_vars);
    for (const auto* st : item->func_body_stmts) {
      WalkStmtsForDeferredActions(st, auto_vars);
    }
  }
}

}  // namespace delta
