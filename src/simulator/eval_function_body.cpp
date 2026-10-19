#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_function_body_internal.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_instance_task.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/pattern_match.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/vpi_design_attach.h"

namespace delta {
// The statement executor for a subroutine body (13.4). A function or task
// body does not run on the scheduler the way a procedural block does: it runs
// to completion within the caller's evaluation, so it needs its own execution
// of every statement form -- declarations, conditionals and loops -- that
// returns as soon as a `return` is reached and takes a `break` or a `continue`
// to the loop it belongs to (§12.8). Those live here;
// eval_function_body_assign.cpp holds the assignment forms the same executor
// dispatches to, and eval_function_args.cpp the argument binding and
// write-back that surround a call.

static FuncFlow ExecFuncBlock(const Stmt* stmt, const FuncExecCtx& exec);

// Returns the trailing unconditional else of an if/else-if chain, or null when
// the chain has no final else.
static const Stmt* FuncFindFinalElse(const Stmt* stmt) {
  const Stmt* cur = stmt;
  while (cur->else_branch && cur->else_branch->kind == StmtKind::kIf) {
    cur = cur->else_branch;
  }
  return cur->else_branch;
}

// Runs the branch selected by a unique-if scan: the first matching arm, else
// the trailing unconditional else, reporting a no-match violation for a plain
// `unique` chain that has no final else.
static FuncFlow ExecFuncUniqueIfBranch(const Stmt* stmt, UniqueIfChain& scan,
                                       CaseQualifier qual,
                                       const FuncExecCtx& exec) {
  if (scan.first_match) {
    if (scan.scoped) exec.ctx.RestoreScope(std::move(scan.bound));
    FuncFlow r = ExecFuncStmt(scan.first_match->then_branch, exec);
    if (scan.scoped) exec.ctx.PopScope();
    return r;
  }
  if (scan.has_final_else) {
    const Stmt* final_else = FuncFindFinalElse(stmt);
    if (final_else) return ExecFuncStmt(final_else, exec);
  } else if (qual == CaseQualifier::kUnique) {
    exec.ctx.AddPendingViolation(stmt->range.start,
                                 "unique if: no condition matched",
                                 Subclause("12.4.2.1"), qual);
  }
  return FuncFlow::kNext;
}

// A unique/unique0/priority if encountered while running a function or task
// body performs the same violation checks as one in a process body (§12.4.2).
// Because the report queue is keyed on the calling process (§12.4.2.2), routing
// the report through AddPendingViolation attributes it to whichever process
// invoked the subroutine; separate callers therefore accumulate and flush
// independently.
static FuncFlow ExecFuncUniqueIf(const Stmt* stmt, CaseQualifier qual,
                                 const FuncExecCtx& exec) {
  UniqueIfChain scan = EvalUniqueIfChain(stmt, exec.ctx, exec.arena);
  if (scan.match_count > 1) {
    exec.ctx.AddPendingViolation(stmt->range.start,
                                 "unique if: multiple conditions matched",
                                 Subclause("12.4.2.1"), qual);
  }
  return ExecFuncUniqueIfBranch(stmt, scan, qual, exec);
}

static FuncFlow ExecFuncPriorityIf(const Stmt* stmt, const FuncExecCtx& exec) {
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    bool scoped = false;
    if (EnterIfPredicate(cur->condition, exec.ctx, exec.arena, scoped)) {
      FuncFlow r = ExecFuncStmt(cur->then_branch, exec);
      if (scoped) exec.ctx.PopScope();
      return r;
    }
    if (scoped) exec.ctx.PopScope();
  }
  if (const Stmt* final_else = FuncFindFinalElse(stmt)) {
    return ExecFuncStmt(final_else, exec);
  }
  exec.ctx.AddPendingViolation(stmt->range.start,
                               "priority if: no condition matched",
                               Subclause("12.4.2.1"), CaseQualifier::kPriority);
  return FuncFlow::kNext;
}

// An if with no unique, unique0 or priority qualifier. §12.6.2: the
// identifiers the predicate's patterns bind are in scope in its later clauses
// and its true arm (EvalMatchesPredicate), not the else.
static FuncFlow ExecFuncPlainIf(const Stmt* stmt, const FuncExecCtx& exec) {
  bool scoped = PatternBindsIdentifiers(stmt->condition);
  if (scoped) exec.ctx.PushScope();
  bool holds = scoped
                   ? EvalMatchesPredicate(stmt->condition, exec.ctx, exec.arena)
                   : EvalExpr(stmt->condition, exec.ctx, exec.arena).IsTruthy();
  FuncFlow r = holds ? ExecFuncStmt(stmt->then_branch, exec) : FuncFlow::kNext;
  if (scoped) exec.ctx.PopScope();
  if (!holds && stmt->else_branch) r = ExecFuncStmt(stmt->else_branch, exec);
  return r;
}

static FuncFlow ExecFuncIf(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(exec.ctx.StmtFrameName(stmt));
  auto qual = stmt->qualifier;
  FuncFlow r =
      (qual == CaseQualifier::kUnique || qual == CaseQualifier::kUnique0)
          ? ExecFuncUniqueIf(stmt, qual, exec)
      : qual == CaseQualifier::kPriority ? ExecFuncPriorityIf(stmt, exec)
                                         : ExecFuncPlainIf(stmt, exec);
  if (labeled) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
  return r;
}

// §9.3.1: the statements of a begin-end block run in order, and control that
// leaves one of them -- a break, a continue or a return -- leaves the block
// with it, for the enclosing loop or the body to act on. §11.12: an unnamed
// block declaring a let is given a frame of its own, so the let ends with it.
static FuncFlow ExecFuncBlock(const Stmt* stmt, const FuncExecCtx& exec) {
  bool named = !stmt->label.empty();
  bool scoped = !named && BlockDeclaresLet(stmt);
  if (named) exec.ctx.PushStaticScope(exec.ctx.StmtFrameName(stmt));
  if (scoped) exec.ctx.PushScope();
  FuncNamedScope scope(stmt->label, exec);
  FuncFlow flow = FuncFlow::kNext;
  for (auto* c : stmt->stmts) {
    flow = ExecFuncStmt(c, exec);
    if (flow != FuncFlow::kNext) break;
  }
  if (named) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
  if (scoped) exec.ctx.PopScope();
  return scope.Leave(flow);
}

// §9.6.2 with its Example 5: a `disable` in a subroutine body naming a named
// block or labeled loop the statement stands in ends that scope -- a
// `continue` when the block is a loop's body, a `break` when it encloses the
// loop. A target outside the body is not the body's to end, and the
// statement goes on to the next.
static FuncFlow ExecFuncDisable(const Stmt* stmt, const FuncExecCtx& exec) {
  if (!stmt->expr || stmt->expr->kind != ExprKind::kIdentifier) {
    return FuncFlow::kNext;
  }
  std::string_view target = stmt->expr->text;
  const auto& scopes = *exec.named_scopes;
  if (std::find(scopes.begin(), scopes.end(), target) == scopes.end()) {
    return FuncFlow::kNext;
  }
  exec.ctx.SetDisableTarget(target);
  return FuncFlow::kDisable;
}

// True when any for-loop init declares a new variable (has an explicit type),
// which requires a fresh scope to hold the loop-local declarations.
static bool ForInitNeedsScope(const Stmt* stmt) {
  for (const auto& t : stmt->for_init_types) {
    if (t.kind != DataTypeKind::kImplicit) return true;
  }
  return false;
}

// Runs the for-loop initializers: typed inits create loop-local variables,
// while untyped inits execute as ordinary statements.
static void ExecFuncForInits(const Stmt* stmt, const FuncExecCtx& exec) {
  for (size_t i = 0; i < stmt->for_inits.size(); ++i) {
    auto* init = stmt->for_inits[i];
    if (i < stmt->for_init_types.size() &&
        stmt->for_init_types[i].kind != DataTypeKind::kImplicit && init &&
        init->lhs && init->lhs->kind == ExprKind::kIdentifier) {
      // §12.7.1: a declared control variable is a local of the type the
      // initialization writes, made as a body local of that type is, and its
      // initializer is its declaration assignment (§6.8).
      CreateFuncLocalVar(init->lhs->text, stmt->for_init_types[i], init->rhs,
                         exec.ctx, exec.arena);
    } else if (init) {
      ExecFuncStmt(init, exec);
    }
  }
}

// Runs the condition/body/step iterations of a for-loop. §12.8: a `continue`
// jumps to the end of the body and the loop's step runs as it does after a
// body that ran to the end; a `break` leaves the loop without the step, and
// a `return` leaves the subroutine. §12.7.1 step b): an omitted expression
// executes the statement, so the loop runs until one of those leaves it; it
// was taken as false, and the body never ran.
static FuncFlow ExecFuncForLoop(const Stmt* stmt, const FuncExecCtx& exec) {
  FuncFlow flow = FuncFlow::kNext;
  while (!stmt->for_cond ||
         EvalExpr(stmt->for_cond, exec.ctx, exec.arena).IsTruthy()) {
    flow = ExecFuncStmt(stmt->for_body, exec);
    if (!LoopGoesOn(flow)) break;
    for (auto* step : stmt->for_steps) ExecFuncStmt(step, exec);
  }
  return LoopExitFlow(flow);
}

static FuncFlow ExecFuncFor(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(exec.ctx.StmtFrameName(stmt));
  FuncNamedScope named(stmt->label, exec);
  bool scoped = ForInitNeedsScope(stmt);
  if (scoped) exec.ctx.PushScope();
  ExecFuncForInits(stmt, exec);
  FuncFlow flow = ExecFuncForLoop(stmt, exec);
  if (scoped) exec.ctx.PopScope();
  if (labeled) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
  return named.Leave(flow);
}

// §12.7.6/§12.8: the body runs while the condition holds; a `continue` goes
// back to the condition, a `break` leaves the loop and a `return` leaves the
// subroutine.
static FuncFlow ExecFuncWhile(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(exec.ctx.StmtFrameName(stmt));
  FuncNamedScope named(stmt->label, exec);
  FuncFlow flow = FuncFlow::kNext;
  while (stmt->condition &&
         EvalExpr(stmt->condition, exec.ctx, exec.arena).IsTruthy()) {
    flow = ExecFuncStmt(stmt->body, exec);
    if (!LoopGoesOn(flow)) break;
  }
  if (labeled) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
  return named.Leave(LoopExitFlow(flow));
}

// §12.7.7/§12.8: the body runs once before the condition is first read; a
// `continue` jumps to the end of the body, so the condition is read after it
// as after a body that ran to the end.
static FuncFlow ExecFuncDoWhile(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(exec.ctx.StmtFrameName(stmt));
  FuncNamedScope named(stmt->label, exec);
  FuncFlow flow = FuncFlow::kNext;
  do {
    flow = ExecFuncStmt(stmt->body, exec);
    if (!LoopGoesOn(flow)) break;
  } while (stmt->condition &&
           EvalExpr(stmt->condition, exec.ctx, exec.arena).IsTruthy());
  if (labeled) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
  return named.Leave(LoopExitFlow(flow));
}

// §12.7.2/§12.8: a `forever` in a subroutine body ends only through a `break`
// or a `return` of its body; there is no timing control to suspend it (§13.4).
// A `repeat` also ends after the count LoopIterationLimit reads.
static FuncFlow ExecFuncRepeatOrForever(const Stmt* stmt,
                                        const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(exec.ctx.StmtFrameName(stmt));
  FuncNamedScope named(stmt->label, exec);
  std::optional<uint64_t> limit =
      LoopIterationLimit(stmt, exec.ctx, exec.arena);
  FuncFlow flow = FuncFlow::kNext;
  for (uint64_t i = 0; !limit || i < *limit; ++i) {
    flow = ExecFuncStmt(stmt->body, exec);
    if (!LoopGoesOn(flow)) break;
  }
  if (labeled) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
  return named.Leave(LoopExitFlow(flow));
}

// Carries out a `return <expr>;`. §13.4.1: the function definition implicitly
// declares a variable internal to the function, of the function's return type,
// so a return is an assignment to a typed object rather than a replacement of
// it. §10.7 then decides the value: the expression is extended or truncated to
// the declared width, extending by the expression's own signedness, and the
// object keeps the signedness its declaration gave it. The other form §13.4.1
// offers -- assigning to the function's name -- goes through the ordinary
// assignment executor and has always done this; a `return` that took the
// expression's vector whole handed the caller a `logic [7:0]` function's result
// 32 bits wide, and let a 1-bit comparison's signedness stand in for an
// `int`'s. §13.4.1 with §10.4: `return X` of a function whose return type is an
// unpacked array assigns X to the implicit variable, as `fn = X` would --
// an array variable's elements copied, an assignment pattern distributed over
// them, a queue rebuilt -- and the body's completion hands that variable's
// elements to the caller (ExecFunctionBody).
static void AssignArrayReturn(const Stmt* stmt, const FuncExecCtx& exec) {
  Expr name;
  name.kind = ExprKind::kIdentifier;
  name.text = exec.func_name;
  name.range = stmt->range;
  Stmt assign;
  assign.kind = StmtKind::kBlockingAssign;
  assign.lhs = &name;
  assign.rhs = stmt->expr;
  assign.range = stmt->range;
  ExecFuncBlockingAssign(&assign, exec.ctx, exec.arena);
}

static void ExecFuncReturn(const Stmt* stmt, const FuncExecCtx& exec) {
  if (exec.array_return) {
    AssignArrayReturn(stmt, exec);
    return;
  }
  // §13.4.1 with §8.7: `return new` constructs an object of the return type
  // into the implicit variable, as `f = new` does; read as a value, the `new`
  // stored null.
  if (TryFuncReturnClassNew(stmt->expr, exec.func_name, exec.ctx, exec.arena))
    return;
  // §6.8, printed page 105: a variable keeps its value from one assignment to
  // the next, so the implicit return variable and the returned one are two
  // storage elements and neither may hold the other's words. EvalExpr answers a
  // bare identifier's, an unpacked element's or a class property's own vector,
  // and ResizeToWidth passes a value already at the declared width straight
  // through, so the CoerceTo2State below would write into whatever was
  // returned -- and a returned `ref` or `output` formal carries that back out
  // to the caller's argument.
  Logic4Vec val = OwnRhsWords(
      EvalExpr(stmt->expr, exec.ctx, exec.arena, exec.ret_var->value.width),
      exec.arena);
  // §13.4.1 with §7.10, §7.5 and §7.4: a return type that is a queue or an
  // array gives the implicit variable elements, which the vector above does
  // not carry -- it is the one-element-wide variable the aggregate's name
  // holds. The elements are copied out here, while the callee's storage still
  // stands, for a `fq().size()` or `fa()[1]` that reads the call as that
  // variable (eval_call_result.cpp); nothing is copied unless such a read is
  // waiting.
  RecordReturnedAggregate(stmt->expr, exec.ctx, exec.arena);
  // §7.3.2 with §13.4.1: `return tagged M v` gives the implicit variable a
  // tagged union value, and its tag travels beside the bits, which the vector
  // above does not carry; the member the expression names is recorded for
  // the caller's binding of the result to a formal (eval_call_result.cpp),
  // where an untagged formal read `a.Valid` of a `tagged Invalid` result
  // against no tag. Nothing is recorded unless such a read is waiting.
  RecordReturnedTag(stmt->expr);
  // §7.3.2 (printed page 151): a tagged union variable's value is its tag
  // beside the member's bits, so `return v` hands out v's tag as much as
  // `return tagged M x` hands out M's -- and §11.9 (printed 304) checks the
  // caller's member reads of what it assigned the call to against it. The
  // tag stands in the table by v's storage key rather than in the vector the
  // return evaluated to, so it is read from there; recorded from a `tagged`
  // expression alone, `u = g()` for a g returning a variable left u's
  // previous tag standing and `u.Other` raised nothing after `tagged Valid`.
  RecordReturnedVariableTag(stmt->expr, exec.ctx);
  if (exec.ret_width != 0) {
    // §6.12.1 with §13.4.1: the store into the implicit variable is an
    // assignment to an object of the return type, so a real function's
    // `return i` of an integer converts the integer into a real, 3.0 for 3,
    // and an integral function's `return r` rounds the real, as `f = expr`
    // does through ConvertRealOnAssign. Resized alone, the integer's bits
    // went out as the double 0.0.
    val = ConvertRealForKnownLhs(val, exec.ret_var->is_real, exec.ret_width,
                                 exec.arena);
    val.is_signed = exec.ret_var->is_signed;
  }
  exec.ret_var->value = val;
  // §6.11.2: §13.4.1 gives the implicit variable the function's return type, so
  // a `return` into a 2-state one converts its unknowns to zeros. The
  // assignment form `f = expr;` is converted by ExecFuncIdentifierAssign, which
  // this statement does not go through.
  if (!exec.ret_var->is_4state) CoerceTo2State(exec.ret_var->value);
}

// §16.4.5: a deferred immediate assertion inside a function is evaluated and
// its report scheduled against the calling process, so each process that calls
// the function reports independently. §16.3: a simple immediate assertion runs
// its pass or fail statement where it stands, and that statement is a
// statement of the function body, a return included. §21.2.1.5: the label is
// a hierarchy level while the statement runs, so a report under it names it.
static FuncFlow ExecFuncImmediateAssert(const Stmt* stmt,
                                        const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushActiveNamedScope(stmt->label);
  const Stmt* action =
      ExecImmediateAssertInFunction(stmt, exec.ctx, exec.arena);
  FuncFlow flow = ExecFuncStmt(action, exec);
  if (labeled) exec.ctx.PopActiveNamedScope();
  return flow;
}

// §13.4: a case statement in a function body selects its item as one in a
// process does and runs the body here, synchronously, with the identifiers
// the item's pattern bound in scope (§12.6.1); answers where control went
// from the body.
static FuncFlow ExecFuncCase(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(exec.ctx.StmtFrameName(stmt));
  CaseSelection chosen = SelectCaseItem(stmt, exec.ctx, exec.arena);
  bool scoped = !chosen.bindings.empty();
  if (scoped) {
    exec.ctx.PushScope();
    InstallPatternBindings(chosen.bindings, exec.ctx);
  }
  FuncFlow flow = ExecFuncStmt(chosen.body, exec);
  if (scoped) exec.ctx.PopScope();
  if (labeled) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
  return flow;
}

// §18.16 with §13.4: a randcase is a statement a function body may hold. The
// branch is the one SelectRandcaseBranch draws, and it runs here as any
// statement of the body does, so a return in it is the function's return and
// a break or continue in it is the enclosing loop's. Left to the default the
// statement did nothing, and a function selecting a branch returned what its
// variables held before it.
static FuncFlow ExecFuncRandcase(const Stmt* stmt, const FuncExecCtx& exec) {
  return ExecFuncStmt(SelectRandcaseBranch(stmt, exec.ctx, exec.arena), exec);
}

// §18.17 with §13.4: a randsequence is a statement a function body may hold,
// and ExecRandsequence in stmt_exec_randsequence.cpp, the engine that
// generates it, is a coroutine driving each code block through the process
// path's ExecStmt. Nothing in a function body suspends (§13.4.4), so the
// engine is run to its end here. §18.17.6 gives a break in a code block the
// randsequence to end and a return there its production, and the engine
// consumes both, so the body goes on to its next statement as a process does.
// Left to the default the statement did nothing, and a function generating a
// sequence returned what its variables held before it.
static FuncFlow ExecFuncRandsequence(const Stmt* stmt,
                                     const FuncExecCtx& exec) {
  ExecRandsequence(stmt, exec.ctx, exec.arena).RunToCompletion();
  return FuncFlow::kNext;
}

FuncFlow ExecFuncStmt(const Stmt* stmt, const FuncExecCtx& exec) {
  if (!stmt) return FuncFlow::kNext;
  switch (stmt->kind) {
    case StmtKind::kReturn:
      if (stmt->expr) ExecFuncReturn(stmt, exec);
      return FuncFlow::kReturn;
    case StmtKind::kBreak:
      return FuncFlow::kBreak;
    case StmtKind::kDisable:
      return ExecFuncDisable(stmt, exec);
    case StmtKind::kContinue:
      return FuncFlow::kContinue;
    case StmtKind::kBlockingAssign:
      ExecFuncBlockingAssign(stmt, exec.ctx, exec.arena);
      return FuncFlow::kNext;
    case StmtKind::kNonblockingAssign:
      // §13.4.4: a nonblocking assignment is legal in a function body; it
      // schedules into the NBA region just as it does in a process, rather
      // than being dropped. The enclosing call runs inside a process, so the
      // scheduler is active to drain the update.
      ExecNonblockingAssignImpl(stmt, exec.ctx, exec.arena);
      return FuncFlow::kNext;
    case StmtKind::kExprStmt:
      // §15.4 and §15.3.3 with §13.4: a mailbox's put(), get() or peek()
      // and a semaphore's get() in a body are served here where they would
      // not wait, since the expression evaluator below answers num(), put()
      // and the try_* forms alone.
      if (!TryExecSystemCallTask(stmt->expr, exec.ctx, exec.arena) &&
          !TryExecMailboxCallInFunction(stmt->expr, exec.ctx, exec.arena) &&
          !TryExecSemaphoreCallInFunction(stmt->expr, exec.ctx, exec.arena)) {
        // §13.5.5: `p.m;` and a bare `m;` name a method as `p.m()` does.
        ExecCallStmtExpr(stmt->expr, exec.ctx, exec.arena);
      }
      return FuncFlow::kNext;
    case StmtKind::kVarDecl:
      ExecFuncVarDecl(stmt, {exec.static_frame, exec.is_static_sub}, exec.ctx,
                      exec.arena);
      return FuncFlow::kNext;
    case StmtKind::kBlockItemDecl:
      ExecBlockItemDeclImpl(stmt, exec.ctx, exec.arena);
      return FuncFlow::kNext;
    case StmtKind::kIf:
      return ExecFuncIf(stmt, exec);
    case StmtKind::kCase:
      return ExecFuncCase(stmt, exec);
    case StmtKind::kBlock:
      return ExecFuncBlock(stmt, exec);
    case StmtKind::kFor:
      return ExecFuncFor(stmt, exec);
    case StmtKind::kForeach:
      return ExecFuncForeach(stmt, exec);
    case StmtKind::kWhile:
      return ExecFuncWhile(stmt, exec);
    case StmtKind::kDoWhile:
      return ExecFuncDoWhile(stmt, exec);
    case StmtKind::kForever:
    case StmtKind::kRepeat:
      return ExecFuncRepeatOrForever(stmt, exec);
    case StmtKind::kEventTrigger:
    case StmtKind::kNbEventTrigger:
      // §13.4.4 names no event trigger among what a function may not hold, and
      // a task reached from a synchronous position -- a deferred assertion's
      // action (§16.4) -- runs here too, so `-> e` fires and `->> e` schedules
      // its update event as they would in a process; left to the default they
      // did nothing, and a process waiting on the event never woke.
      ExecEventTriggerInFunction(stmt, exec.ctx, exec.arena);
      return FuncFlow::kNext;
    case StmtKind::kFork:
      // §13.4.4: a function may fork off background processes with join_none
      // (join/join_any would block and are illegal here). Spawn the children
      // and continue; the function itself does not wait.
      SpawnForkJoinNone(stmt, exec.ctx, exec.arena);
      return FuncFlow::kNext;
    case StmtKind::kAssertImmediate:
    case StmtKind::kAssumeImmediate:
    case StmtKind::kCoverImmediate:
      return ExecFuncImmediateAssert(stmt, exec);
    case StmtKind::kRandcase:
      return ExecFuncRandcase(stmt, exec);
    case StmtKind::kRandsequence:
      return ExecFuncRandsequence(stmt, exec);
    default:
      return FuncFlow::kNext;
  }
}

// §13.4.1: a function may return a structure or a union, and a hierarchical
// name inside the function beginning with the function's name is a member of
// the return value, so `mk.a = 3` in `function st_t mk()` writes the member
// `a` of the implicit variable and `return mk`, or falling off the end, hands
// the members out. The implicit variable is created at the return type's width
// alone (EvalFunctionCall, ExecClassMethod), and the member window §7.2 makes
// of `mk.a` is read off the layout SimContext holds for a variable's name
// (ResolveFieldTarget, ResolveMemberByType), which nothing recorded for the
// function's: the write resolved to no member and the caller read zeros
// (#3809). The layout a typedef name stands for is registered under that name
// by RegisterDesignTypeLayouts, for a packed and an unpacked structure alike,
// so the implicit variable's name is bound to it as a declared variable's is.
// A return type that is no structure -- or one written inline, which has no
// name the table could hold -- records nothing, and the body runs as before.
static void BindReturnStructLayout(const ModuleItem* func, SimContext& ctx) {
  BindNamedLayout(func->name, func->return_type, ctx);
}

// §13.4.1 with §7.4, §7.5 and §7.10: a function whose return type names a
// typedef of an unpacked array, `function a_t fn()` under `typedef int
// a_t[3]`, has an implicit variable of that type, which the body may write
// element by element, `fn[1] = 8`, or through the array's methods,
// `qn.push_back(4)`. It is made here as a local declaration of the type would
// be (CreateDeclAggregate), from the dimensions and element type the
// elaborator recorded (ModuleItem::return_array_dims). Answers whether it made
// one; made one element wide, as the implicit variable of any return type is,
// such writes found no element and the caller read nothing.
static bool ShapeArrayReturnVariable(const ModuleItem* func, SimContext& ctx,
                                     Arena& arena) {
  if (func->return_array_dims.empty()) return false;
  Stmt decl;
  decl.kind = StmtKind::kVarDecl;
  decl.var_name = func->name;
  decl.var_decl_type = func->return_array_elem_type;
  decl.var_unpacked_dims = func->return_array_dims;
  uint32_t width = DeclaredTypeWidth(decl.var_decl_type, ctx);
  CreateDeclAggregate(&decl, width == 0 ? 32 : width, ctx, arena);
  // §7.2: elements that are structures are laid out by their type under the
  // array's name, as a local array of them is, so their members are written
  // and read, and the caller's `mk()[1].y` reads its member.
  BindNamedLayout(func->name, func->return_array_elem_type, ctx);
  return true;
}

void ExecFunctionBody(const ModuleItem* func, const Expr* call,
                      Variable* ret_var, SimContext& ctx, Arena& arena) {
  // §37.44 detail 1: a thread going down a chain of task and function calls
  // activates a new frame on entering each one. This is that entry for a
  // function or a method, and the scope is what leaves the frame that was
  // active standing again however the body ends
  // -- a return out of the middle of it included.
  VpiActiveFrameScope frame(call);
  // §13.4.1: the record a `return` of a queue or an array fills, handed to
  // the evaluation of the call when the body completes (eval_call_result.cpp).
  FunctionBodyResultScope result_scope(ctx);
  // A return type nothing can size -- void, a string, a class handle, a
  // parameterized method's type -- leaves the return statement to take the
  // expression's own vector, which is what it has always done. A typedef name
  // is sized, through the type_widths table, so §13.4.1's implicit variable
  // holds the width the name declares rather than the returned expression's.
  uint32_t ret_width =
      DeclaredTypeWidth(func->return_type, ctx) == 0 ? 0 : ret_var->value.width;
  // §13.4.1 with §6.16: a string return type gives the implicit variable no
  // width, shaped as a body local's (eval_function_body_assign.cpp).
  ShapeStringReturnVariable(func, ret_var, ctx, arena);
  // §13.4.1 with §8.7: a class return type gives it the class a `new` in the
  // body constructs, recorded as a body local's is.
  ShapeClassReturnVariable(func, ret_var, ctx, arena);
  StaticLocalFrameScope static_frame(func, ctx, arena);
  std::vector<std::string_view> named_scopes;
  FuncExecCtx exec{ret_var,
                   func->name,
                   static_frame.Name(),
                   ctx,
                   arena,
                   ret_width,
                   func->is_static && !func->is_automatic,
                   &named_scopes};
  BindReturnStructLayout(func, ctx);
  exec.array_return = ShapeArrayReturnVariable(func, ctx, arena);
  // §12.8 allows a break or a continue only inside a loop, so one that reaches
  // the body's own statement list has no loop to act on it; the body ends
  // there, as it does at a return, rather than going on as if the statement
  // had not been written.
  for (auto* s : func->func_body_stmts) {
    if (ExecFuncStmt(s, exec) != FuncFlow::kNext) break;
  }
  // §13.4.1: whether the body ended at a `return` or fell off its end, the
  // implicit variable holds the result, and its elements are handed to an
  // evaluation of the call that asks for them (eval_call_result.cpp).
  if (exec.array_return) {
    Expr name;
    name.kind = ExprKind::kIdentifier;
    name.text = func->name;
    RecordReturnedAggregate(&name, ctx, arena);
  }
}

}  // namespace delta
