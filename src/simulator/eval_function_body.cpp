#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_instance_task.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
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

// The environment in which a subroutine body executes (§13.4): the return
// variable that a `return` writes, the subroutine name used to key static
// function-local variables (§13.4.2), and the simulation/evaluation context.
// This quartet travels together through the entire recursive statement
// executor, so it is bundled into one entity rather than passed field by
// field.
struct FuncExecCtx {
  Variable* ret_var;
  std::string_view func_name;
  SimContext& ctx;
  Arena& arena;
  // The declared width of the return value, or zero where the return type has
  // no packed width -- void, a string, a class handle, a parameterized method's
  // type. ExecFuncReturn reads zero as "leave the expression's own vector
  // alone".
  uint32_t ret_width;
};

// Where control goes once a statement of the body has run (§12.8): on to
// the statement after it, out of the innermost enclosing loop (`break`), to
// the end of the innermost enclosing loop's body (`continue`), or out of the
// subroutine (`return`). Every executor here answers one of these; a block,
// a conditional and a case hand up whatever the statement they ran answered,
// a loop consumes kBreak and kContinue and hands up kReturn, and
// ExecFunctionBody stops at anything but kNext. Before this the executors
// answered a bool meaning "a return ran", and a break or continue reached
// nothing that acted on it: uvm_report_server::reset_severity_counts, a
// `forever` over an enumeration that breaks at its last member, never ended.
enum class FuncFlow : uint8_t { kNext, kBreak, kContinue, kReturn };

static FuncFlow ExecFuncStmt(const Stmt* stmt, const FuncExecCtx& exec);
static FuncFlow ExecFuncBlock(const Stmt* stmt, const FuncExecCtx& exec);

// §12.8: a loop goes on to its next iteration when its body ran to the end or
// reached a `continue`; a `break` or a `return` ends the iterating.
static bool LoopGoesOn(FuncFlow flow) {
  return flow == FuncFlow::kNext || flow == FuncFlow::kContinue;
}

// What a loop answers once it has stopped iterating, given what its body
// answered last: a `return` leaves the subroutine and so passes through, and
// a `break`, a `continue` or a body that ran to the end is consumed by the
// loop, which is then followed by the statement after it.
static FuncFlow LoopExitFlow(FuncFlow last) {
  return last == FuncFlow::kReturn ? FuncFlow::kReturn : FuncFlow::kNext;
}

// Returns the trailing unconditional else of an if/else-if chain, or null when
// the chain has no final else.
static const Stmt* FuncFindFinalElse(const Stmt* stmt) {
  const Stmt* cur = stmt;
  while (cur->else_branch && cur->else_branch->kind == StmtKind::kIf) {
    cur = cur->else_branch;
  }
  return cur->else_branch;
}

// Aggregated result of evaluating the conditions of a unique-if chain.
struct UniqueIfScan {
  int match_count = 0;
  const Stmt* first_match = nullptr;
  bool has_final_else = false;
};

// Evaluates every condition in the if/else-if chain in source order, recording
// how many matched, the first match, and whether the chain ends in a final
// else.
static UniqueIfScan ScanUniqueIfChain(const Stmt* stmt, SimContext& ctx,
                                      Arena& arena) {
  UniqueIfScan scan;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    if (EvalExpr(cur->condition, ctx, arena).IsTruthy()) {
      scan.match_count++;
      if (!scan.first_match) scan.first_match = cur;
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      scan.has_final_else = true;
    }
  }
  return scan;
}

// Runs the branch selected by a unique-if scan: the first matching arm, else
// the trailing unconditional else, reporting a no-match violation for a plain
// `unique` chain that has no final else.
static FuncFlow ExecFuncUniqueIfBranch(const Stmt* stmt,
                                       const UniqueIfScan& scan,
                                       CaseQualifier qual,
                                       const FuncExecCtx& exec) {
  if (scan.first_match) {
    return ExecFuncStmt(scan.first_match->then_branch, exec);
  }
  if (scan.has_final_else) {
    const Stmt* final_else = FuncFindFinalElse(stmt);
    if (final_else) return ExecFuncStmt(final_else, exec);
  } else if (qual == CaseQualifier::kUnique) {
    exec.ctx.AddPendingViolation(stmt->range.start,
                                 "unique if: no condition matched",
                                 Subclause("12.4.2.1"));
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
  UniqueIfScan scan = ScanUniqueIfChain(stmt, exec.ctx, exec.arena);
  if (scan.match_count > 1) {
    exec.ctx.AddPendingViolation(stmt->range.start,
                                 "unique if: multiple conditions matched",
                                 Subclause("12.4.2.1"));
  }
  return ExecFuncUniqueIfBranch(stmt, scan, qual, exec);
}

static FuncFlow ExecFuncPriorityIf(const Stmt* stmt, const FuncExecCtx& exec) {
  bool has_final_else = false;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    if (EvalExpr(cur->condition, exec.ctx, exec.arena).IsTruthy()) {
      return ExecFuncStmt(cur->then_branch, exec);
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      has_final_else = true;
    }
  }
  if (has_final_else) {
    const Stmt* final_else = FuncFindFinalElse(stmt);
    if (final_else) return ExecFuncStmt(final_else, exec);
  } else {
    exec.ctx.AddPendingViolation(stmt->range.start,
                                 "priority if: no condition matched",
                                 Subclause("12.4.2.1"));
  }
  return FuncFlow::kNext;
}

static FuncFlow ExecFuncIf(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);

  auto qual = stmt->qualifier;
  FuncFlow r = FuncFlow::kNext;
  if (qual == CaseQualifier::kUnique || qual == CaseQualifier::kUnique0) {
    r = ExecFuncUniqueIf(stmt, qual, exec);
  } else if (qual == CaseQualifier::kPriority) {
    r = ExecFuncPriorityIf(stmt, exec);
  } else {
    auto cond = EvalExpr(stmt->condition, exec.ctx, exec.arena);
    if (cond.ToUint64() != 0) {
      r = ExecFuncStmt(stmt->then_branch, exec);
    } else if (stmt->else_branch) {
      r = ExecFuncStmt(stmt->else_branch, exec);
    }
  }

  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return r;
}

// §9.3.1: the statements of a begin-end block run in order, and control that
// leaves one of them -- a break, a continue or a return -- leaves the block
// with it, for the enclosing loop or the body to act on.
static FuncFlow ExecFuncBlock(const Stmt* stmt, const FuncExecCtx& exec) {
  bool named = !stmt->label.empty();
  if (named) exec.ctx.PushStaticScope(stmt->label);
  FuncFlow flow = FuncFlow::kNext;
  for (auto* c : stmt->stmts) {
    flow = ExecFuncStmt(c, exec);
    if (flow != FuncFlow::kNext) break;
  }
  if (named) exec.ctx.PopStaticScope(stmt->label);
  return flow;
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
      uint32_t w = EvalTypeWidth(stmt->for_init_types[i]);
      if (w == 0) w = 32;
      // §6.11.3: byte, shortint, int, integer and longint default to signed,
      // so the declared type decides the loop variable's signedness as it
      // decides any other local's. Created from the width alone, an int
      // counter compared its negative values as huge positive ones.
      auto* v = exec.ctx.CreateLocalVariable(
          init->lhs->text, w,
          DeclaredTypeIsSigned(stmt->for_init_types[i], exec.ctx));
      // §6.11.2: the declared type decides whether the loop variable can hold
      // an unknown at all -- "when a 4-state value is automatically converted
      // to a 2-state value, any unknown or high-impedance bits shall be
      // converted to zeros" -- and the flag defaults to true, so an `int`
      // counter kept the x and z its initializer read. CreateFuncLocalVar sets
      // the same flag for an ordinary body local from the same answer.
      v->is_4state = DeclaredTypeIs4State(stmt->for_init_types[i]);
      // §10.7 sizes the right-hand side to the left-hand side, and the width
      // the type declares reached the cell CreateLocalVariable made and was
      // then thrown away by the store: a Logic4Vec carries its own width, so
      // `for (int i = seed; ...)` over a `logic [7:0] seed` left i eight bits
      // wide for every later read, step and comparison. The initializer is
      // copied for the reason CreateFuncLocalVar copies its own (§6.8): `for
      // (int i = n; ...)` would otherwise leave i and n one storage element,
      // and the loop's own step is the store that shows it. The copy goes
      // outside the resize because ResizeToWidth answers its argument
      // untouched when the widths already match, which is precisely the
      // aliased case, and the coercion below writes in place -- through a
      // shared buffer it would clear the source variable's own unknown bits.
      if (init->rhs) {
        v->value =
            OwnRhsWords(ResizeToWidth(EvalExpr(init->rhs, exec.ctx, exec.arena),
                                      w, exec.arena),
                        exec.arena);
        if (!v->is_4state) CoerceTo2State(v->value);
      }
    } else if (init) {
      ExecFuncStmt(init, exec);
    }
  }
}

// Runs the condition/body/step iterations of a for-loop. §12.8: a `continue`
// jumps to the end of the body and the loop's step runs as it does after a
// body that ran to the end; a `break` leaves the loop without the step, and
// a `return` leaves the subroutine.
static FuncFlow ExecFuncForLoop(const Stmt* stmt, const FuncExecCtx& exec) {
  FuncFlow flow = FuncFlow::kNext;
  while (stmt->for_cond &&
         EvalExpr(stmt->for_cond, exec.ctx, exec.arena).IsTruthy()) {
    flow = ExecFuncStmt(stmt->for_body, exec);
    if (!LoopGoesOn(flow)) break;
    for (auto* step : stmt->for_steps) ExecFuncStmt(step, exec);
  }
  return LoopExitFlow(flow);
}

static FuncFlow ExecFuncFor(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  bool scoped = ForInitNeedsScope(stmt);
  if (scoped) exec.ctx.PushScope();
  ExecFuncForInits(stmt, exec);
  FuncFlow flow = ExecFuncForLoop(stmt, exec);
  if (scoped) exec.ctx.PopScope();
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return flow;
}

static std::string GetForeachArrayName(const Expr* expr) {
  if (!expr) return {};
  if (expr->kind == ExprKind::kIdentifier) return std::string(expr->text);
  if (expr->kind == ExprKind::kMemberAccess) {
    std::string name;
    BuildLhsName(expr, name);
    return name;
  }
  return {};
}

// §12.7.6/§12.8: the body runs while the condition holds; a `continue` goes
// back to the condition, a `break` leaves the loop and a `return` leaves the
// subroutine.
static FuncFlow ExecFuncWhile(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  FuncFlow flow = FuncFlow::kNext;
  while (stmt->condition &&
         EvalExpr(stmt->condition, exec.ctx, exec.arena).IsTruthy()) {
    flow = ExecFuncStmt(stmt->body, exec);
    if (!LoopGoesOn(flow)) break;
  }
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return LoopExitFlow(flow);
}

// §12.7.7/§12.8: the body runs once before the condition is first read; a
// `continue` jumps to the end of the body, so the condition is read after it
// as after a body that ran to the end.
static FuncFlow ExecFuncDoWhile(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  FuncFlow flow = FuncFlow::kNext;
  do {
    flow = ExecFuncStmt(stmt->body, exec);
    if (!LoopGoesOn(flow)) break;
  } while (stmt->condition &&
           EvalExpr(stmt->condition, exec.ctx, exec.arena).IsTruthy());
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return LoopExitFlow(flow);
}

// §12.7.2/§12.8: a `forever` in a subroutine body ends only through a `break`
// or a `return` of its body; there is no timing control to suspend it (§13.4).
static FuncFlow ExecFuncForever(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  FuncFlow flow = FuncFlow::kNext;
  for (;;) {
    flow = ExecFuncStmt(stmt->body, exec);
    if (!LoopGoesOn(flow)) break;
  }
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return LoopExitFlow(flow);
}

// Resolves the iteration count for a foreach over the named array: the array's
// element count when known, otherwise the bit width of a matching variable.
static uint32_t ResolveForeachSize(std::string_view name, SimContext& ctx) {
  auto* info = ctx.FindArrayInfo(name);
  if (info) return info->size;
  auto* var = ctx.FindVariable(name);
  return var ? var->value.width : 0;
}

// The index values a foreach in a subroutine body steps through: the keys of
// an associative array, §12.7.3 giving the loop variable the index type and
// the traversal the array's own order, or `size` indices from `lo` up for any
// other array.
static std::vector<Logic4Vec> ForeachIndexValues(const Stmt* stmt,
                                                 const FuncExecCtx& exec) {
  if (auto* aa = FindAssocArrayOfBase(stmt->expr, exec.ctx, exec.arena)) {
    return AssocIndexValues(aa, exec.arena);
  }
  // §12.7.3 with §7.10: a queue's one dimension holds as many elements as the
  // queue does, whether the queue is a declared one or a property of an
  // object (§8.5) named bare in the method or through a handle; a declared
  // dynamic array is stored the same way and answers the same.
  uint32_t size = 0;
  int64_t lo = 0;
  ClassArrayRef ref;
  if (const QueueObject* q =
          FindQueueOfBase(stmt->expr, exec.ctx, exec.arena)) {
    size = static_cast<uint32_t>(q->elements.size());
  } else if (ResolveClassArray(stmt->expr, exec.ctx, exec.arena, ref)) {
    // §12.7.3 with §7.4.2 and §7.5: a fixed-size or dynamic array property
    // (§8.5) holds its elements on the object, the declared dimension's count
    // from its lowest index for a fixed one and the object's count from 0 for
    // a dynamic one, which is what the loop variable steps through. Before
    // this the property was looked up as a variable of its name, which it is
    // not, and the loop ran no times.
    size = ref.size;
    lo = ref.lo;
  } else {
    std::string name = GetForeachArrayName(stmt->expr);
    size = name.empty() ? 0 : ResolveForeachSize(name, exec.ctx);
  }
  std::vector<Logic4Vec> values;
  values.reserve(size);
  for (uint32_t i = 0; i < size; ++i) {
    values.push_back(
        MakeLogic4VecVal(exec.arena, 32, static_cast<uint64_t>(lo + i)));
  }
  return values;
}

// Runs the iteration loop of a foreach over the index values `keys`, pushing
// a scope that holds the (optional) loop index variable. §12.8: a `continue`
// goes on to the next element, a `break` leaves the loop and a `return`
// leaves the subroutine.
static FuncFlow ExecFuncForeachLoop(const Stmt* stmt,
                                    const std::vector<Logic4Vec>& keys,
                                    bool string_keys, const FuncExecCtx& exec) {
  std::string_view iter_name;
  if (!stmt->foreach_vars.empty() && !stmt->foreach_vars[0].empty()) {
    iter_name = stmt->foreach_vars[0];
  }

  exec.ctx.PushScope();
  Variable* iter_var = nullptr;
  if (!iter_name.empty()) {
    iter_var = exec.ctx.CreateLocalVariable(iter_name, 32);
    iter_var->is_string = string_keys;
  }

  FuncFlow flow = FuncFlow::kNext;
  for (const auto& key : keys) {
    if (iter_var) iter_var->value = key;
    flow = ExecFuncStmt(stmt->body, exec);
    if (!LoopGoesOn(flow)) break;
  }

  exec.ctx.PopScope();
  return LoopExitFlow(flow);
}

static FuncFlow ExecFuncForeach(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  auto* aa = FindAssocArrayOfBase(stmt->expr, exec.ctx, exec.arena);
  std::vector<Logic4Vec> keys = ForeachIndexValues(stmt, exec);
  FuncFlow flow = FuncFlow::kNext;
  if (!keys.empty()) {
    flow = ExecFuncForeachLoop(stmt, keys, aa != nullptr && aa->is_string_key,
                               exec);
  }
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return flow;
}

// Carries out a `return <expr>;`. §13.4.1: the function definition implicitly
// declares a variable internal to the function, and "this variable has the same
// type as the function return value", so a return is an assignment to a typed
// object rather than a replacement of it. §10.7 then decides the value: the
// expression is extended or truncated to the declared width, extending by the
// expression's own signedness, and the object keeps the signedness its
// declaration gave it. The other form §13.4.1 offers -- assigning to the
// function's name -- goes through the ordinary assignment executor and has
// always done this; a `return` that took the expression's vector whole handed
// the caller a `logic [7:0]` function's result 32 bits wide, and let a 1-bit
// comparison's signedness stand in for an `int`'s.
static void ExecFuncReturn(const Stmt* stmt, const FuncExecCtx& exec) {
  // §13.4.1 with §8.7: `return new` constructs an object of the return type
  // into the implicit variable, as `f = new` does; read as a value, the `new`
  // stored null.
  if (TryFuncReturnClassNew(stmt->expr, exec.func_name, exec.ctx, exec.arena))
    return;
  // §6.8, printed page 105: a variable "shall store a value from one assignment
  // to the next", so the implicit return variable and the returned one are two
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
// process does and runs the body here, synchronously; answers where control
// went from the body.
static FuncFlow ExecFuncCase(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  const Stmt* body = SelectCaseBody(stmt, exec.ctx, exec.arena);
  FuncFlow flow = ExecFuncStmt(body, exec);
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return flow;
}

static FuncFlow ExecFuncStmt(const Stmt* stmt, const FuncExecCtx& exec) {
  if (!stmt) return FuncFlow::kNext;
  switch (stmt->kind) {
    case StmtKind::kReturn:
      if (stmt->expr) ExecFuncReturn(stmt, exec);
      return FuncFlow::kReturn;
    case StmtKind::kBreak:
      return FuncFlow::kBreak;
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
      ExecFuncVarDecl(stmt, exec.func_name, exec.ctx, exec.arena);
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
      return ExecFuncForever(stmt, exec);
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

void ExecFunctionBody(const ModuleItem* func, Variable* ret_var,
                      SimContext& ctx, Arena& arena) {
  // §37.44 detail 1: "as a thread works its way down a call chain of tasks
  // and/or functions, a new frame is activated as each new task or function is
  // entered". This is that entry for a function or a method, and the scope is
  // what leaves the frame that was active standing again however the body ends
  // -- a return out of the middle of it included.
  VpiActiveFrameScope frame;
  // §13.4.1: the record a `return` of a queue or an array fills, handed to
  // the evaluation of the call when the body completes (eval_call_result.cpp).
  FunctionBodyResultScope result_scope;
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
  FuncExecCtx exec{ret_var, func->name, ctx, arena, ret_width};
  BindReturnStructLayout(func, ctx);
  // §12.8 allows a break or a continue only inside a loop, so one that reaches
  // the body's own statement list has no loop to act on it; the body ends
  // there, as it does at a return, rather than going on as if the statement
  // had not been written.
  for (auto* s : func->func_body_stmts) {
    if (ExecFuncStmt(s, exec) != FuncFlow::kNext) return;
  }
}

}  // namespace delta
