#include <algorithm>
#include <format>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

using SequenceDeclMap = std::unordered_map<std::string_view, const ModuleItem*>;

// §16.8: an instance of a named sequence shall provide an actual argument for
// each formal argument that does not have a default actual argument declared.
// This checks the positional-binding form of an instance used in an event
// control; named or partially-omitted binding is left to the general
// argument-binding machinery.
static void CheckSequenceActualArgCount(Stmt* s, const Expr* call,
                                        const ModuleItem* decl,
                                        DiagEngine& diag) {
  // Only the purely-positional, fully-supplied form is validated here: a named
  // binding populates arg_names, and an omitted actual leaves a null arg.
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

// Mark a single event-control event that names a known sequence, flag the
// §9.4.2.4 automatic-variable argument restriction, and enforce the §16.8
// actual-argument count rule (`s` supplies the location).
// §16.13: what a sequence used as an event is resolved against -- the named
// sequences visible in the scope, their declarations (for the actual-argument
// count check), whether the enclosing subroutine is automatic, and where a
// violation is reported.
struct SequenceEventCtx {
  const std::unordered_set<std::string_view>& seq_names;
  const SequenceDeclMap& seq_decls;
  bool in_automatic;
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

  if (has_args && ctx.in_automatic) {
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
  // §9.4.2.4 requires the arguments of a sequence used as an event control to
  // be static, and §16.8 requires an actual for every formal that has no
  // default. Neither names a statement the requirement is lifted in, so this
  // descends every link ForEachChildStmt in elaborator_validate_internal.h
  // names. It wrote out six of the thirteen, so an `@(s(a, b))` standing in a
  // fork arm, a randcase arm, an assertion action block or a randsequence code
  // block was neither marked a sequence event nor argument-counted.
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtsForSequenceEvents(sub, ctx); });
}

// Walk one module item's statements for sequence-event arguments. A process
// block's statements live in item->body; a task body's statements live in
// func_body_stmts (item->body is the module-process body form), so both are
// walked for a task so an event control such as @(s(a, b)) inside an automatic
// task is reached. §9.4.2.4: arguments to a sequence used in an event control
// shall be static, so an automatic task local passed as a sequence argument is
// an error (in_automatic is false for a process block and a non-automatic
// task, so static sequence arguments stay legal there).
static void WalkItemForSequenceEvents(
    const ModuleItem* item,
    const std::unordered_set<std::string_view>& seq_names,
    const SequenceDeclMap& seq_decls, DiagEngine& diag) {
  if (IsProceduralItemKind(item->kind)) {
    if (item->body) {
      WalkStmtsForSequenceEvents(const_cast<Stmt*>(item->body),
                                 {seq_names, seq_decls, false, diag});
    }
    return;
  }
  if (item->kind != ModuleItemKind::kTaskDecl) return;
  const SequenceEventCtx kCtx{seq_names, seq_decls, item->is_automatic, diag};
  if (item->body) {
    WalkStmtsForSequenceEvents(const_cast<Stmt*>(item->body), kCtx);
  }
  for (auto* s : item->func_body_stmts) {
    WalkStmtsForSequenceEvents(s, kCtx);
  }
}

void Elaborator::ValidateSequenceEventArgs(const ModuleDecl* decl) {
  if (sequence_names_.empty()) return;
  // §16.8 actual-argument checks need each named sequence's formals, so map the
  // sequences declared in this scope by name. A sequence instantiated across a
  // scope boundary is absent here, and its count check is simply skipped.
  SequenceDeclMap seq_decls;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) {
      seq_decls[item->name] = item;
    }
  }
  for (const auto* item : decl->items) {
    WalkItemForSequenceEvents(item, sequence_names_, seq_decls, diag_);
  }
}

static bool IsSingleSubroutineCall(const Stmt* action) {
  if (!action) return true;
  if (action->kind == StmtKind::kNull) return true;
  if (action->kind != StmtKind::kExprStmt) return false;
  if (!action->expr) return false;
  return action->expr->kind == ExprKind::kCall ||
         action->expr->kind == ExprKind::kSystemCall;
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
  // §16.4 refuses a final deferred assertion whose callee body holds a
  // statement the Postponed region cannot run, and it names no statement
  // position the restriction is suspended in, so this descends every link
  // ForEachChildStmt in elaborator_validate_internal.h names. It wrote out six
  // of the thirteen, so an assignment or a timing control written in a fork
  // arm, a for header, an assertion action block, a randcase arm or a
  // randsequence code block left the callee looking legal in the Postponed
  // region.
  //
  // ForEachChildStmt gives the visitor no way to stop, so the first offending
  // statement is kept in `found` and the recursion runs only while `found` is
  // false.
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
  if (!IsSingleSubroutineCall(action)) return;
  if (!action || action->kind != StmtKind::kExprStmt || !action->expr) return;
  if (action->expr->kind != ExprKind::kCall) return;
  auto it = subs.find(action->expr->callee);
  if (it == subs.end()) return;
  if (CalleeBodyHasPostponedIllegal(it->second)) {
    diag.Warning(action->range.start,
                 std::format("final deferred assertion calls '{}', whose body "
                             "contains statements not legally callable in the "
                             "Postponed region (§4.4.2.9)",
                             action->expr->callee),
                 Subclause("16.4"));
  }
}

// §16.4: neither a dynamic variable (e.g. a class property, reached through a
// member access) nor an automatic variable may be the actual for a
// pass-by-reference formal of a deferred-assertion action call -- the storage
// of either may no longer exist when the deferred action runs.
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
  // A bare identifier naming an automatic variable in scope -- a formal or
  // local of the enclosing automatic subroutine -- is the automatic case.
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
  if (!IsSingleSubroutineCall(action)) return;
  if (!action || action->kind != StmtKind::kExprStmt || !action->expr) return;
  if (action->expr->kind != ExprKind::kCall) return;
  auto it = subs.find(action->expr->callee);
  if (it == subs.end()) return;
  const auto& formals = it->second->func_args;
  const auto& actuals = action->expr->args;
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
  // §16.4: "The pass and fail statements in a deferred assertion's
  // action_block, if present, shall each consist of a single subroutine call."
  // §1.5 defines shall as a mandatory requirement "from which no deviation is
  // permitted", so an action block of any other shape is not legal source. It
  // is reported as an error rather than a warning because there is no behaviour
  // left to fall back on: §16.4.1 defers a report by remembering "the
  // associated subroutine call" and executing it in a later region, and a
  // statement that is not a call gives that machinery nothing to remember.
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

// §16.4: gather the names of automatic variables visible to deferred assertions
// in a subroutine body. When the enclosing task or function has automatic
// lifetime, every local variable is automatic; an explicitly-automatic local is
// automatic even inside a static routine.
static void CollectAutomaticVarNames(
    const Stmt* s, bool routine_is_automatic,
    std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl &&
      (routine_is_automatic || s->var_is_automatic)) {
    out.insert(s->var_name);
  }
  // §16.4 bars an automatic variable as the actual for a pass-by-reference
  // formal of a deferred-assertion action call, and it puts no condition on the
  // statement the variable is declared under, so this descends every link
  // ForEachChildStmt in elaborator_validate_internal.h names. It wrote out
  // eight of the thirteen, so an automatic declared in a fork arm, under a
  // randcase arm or in a randsequence code block was never collected and
  // passing it by reference was allowed. A.6.8 admits in a for_initialization
  // and a for_step_assignment only an assignment, an increment or a call, so no
  // declaration stands in either; they are descended all the same because this
  // walk names no link itself.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CollectAutomaticVarNames(sub, routine_is_automatic, out);
  });
}

void Elaborator::WalkStmtsForDeferredActions(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars) {
  if (!s) return;
  CheckDeferredActionStmt(s, deferred_subroutine_map_, auto_vars, diag_);
  // §16.4 states the shape a deferred assertion's action block takes and the
  // actuals its subroutine call may pass, and it names no statement position
  // either rule is lifted in, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h names. It wrote out eight of the thirteen,
  // so a deferred assertion written in a fork arm, under a randcase arm or in a
  // randsequence code block was checked for neither. A.6.8 admits no statement
  // in a for header, so a deferred assertion cannot stand in for_inits or in
  // for_steps; both are descended all the same because this walk names no link
  // itself.
  ForEachChildStmt(s, [this, &auto_vars](Stmt* const& sub) {
    WalkStmtsForDeferredActions(sub, auto_vars);
  });
}

// §16.4: the automatic-variable names in scope for one module item, so a
// deferred action call passing one of them by reference can be rejected. An
// automatic task or function makes its formals and its locals automatic.
static std::unordered_set<std::string_view> CollectItemAutomaticVarNames(
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

void Elaborator::ValidateDeferredAssertionActions(const ModuleDecl* decl) {
  deferred_subroutine_map_.clear();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      deferred_subroutine_map_[item->name] = item;
    }
  }
  for (const auto* item : decl->items) {
    // A task or function keeps its body in func_body_stmts; procedural blocks
    // (initial/always) keep theirs in body. Validate whichever this item uses.
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
