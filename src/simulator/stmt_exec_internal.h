#pragma once

#include <cstdint>

#include "simulator/exec_task.h"
#include "simulator/stmt_result.h"

namespace delta {

struct Stmt;
struct Logic4Vec;
class SimContext;
class Arena;

// Defined in stmt_exec_wait.cpp. Applies the §9.4.1 delay-control value
// rules (unknown/high-impedance delay reads as zero; a negative delay is
// reinterpreted as a two's-complement unsigned integer the width of a time
// variable) to a delay expression's evaluated value. Shared so the
// intra-assignment delay of a blocking assignment (§10.4.1) normalizes its
// delay the same way a standalone delay-control statement does.
uint64_t DelayTicksFromValue(const Logic4Vec& val);

// Defined in stmt_exec_wait.cpp. Turns a delay expression's evaluated value
// into the scheduler tick count that a delay control waits for, applying the
// §3.14.1 time-value rounding rule: the delay is rounded to the time precision
// of the design element that issues it (a real delay keeps only the fractional
// digits its precision allows), then expressed in ticks of the design's global
// precision. Shared so a standalone delay-control statement (§9.4.1) and the
// intra-assignment delay of a blocking assignment (§10.4.1) round identically.
uint64_t DelayValueToTicks(const Logic4Vec& val, const SimContext& ctx);

// Statement executors split out of stmt_exec.cpp into sibling translation
// units. The dispatcher in stmt_exec.cpp calls these by name, so they have
// external linkage and are declared here rather than as file-local statics.

// Defined in stmt_exec_randsequence.cpp.
// §18.16: the branch one execution of a randcase takes -- its weights
// evaluated once each, a number drawn below their sum, the item whose
// cumulative weight the number falls under -- or null when every weight is
// zero, which is warned of here. Shared by ExecRandcase and the function-body
// path in eval_function_body.cpp, which runs the branch as it runs any
// statement of the body, so that a return in the branch is the function's.
const Stmt* SelectRandcaseBranch(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena);
ExecTask ExecRandcase(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecRandsequence(const Stmt* stmt, SimContext& ctx, Arena& arena);

// Defined in stmt_exec_wait.cpp.
// §13.3 with §8.6: runs the body of an instance task enabled through a
// handle, `h.t(...)`, whose frame SetupInstanceTaskCall (eval_instance_task.h)
// has pushed, and tears the frame down when the body has completed. Defined in
// stmt_exec_class_task.cpp.
struct Expr;
struct InstanceMethodInfo;
ExecTask ExecInstanceTaskCall(const InstanceMethodInfo& call, const Expr* expr,
                              SimContext& ctx, Arena& arena);
// A blocking assignment with no intra-assignment timing control, executed at
// once. Inside a class method -- an instance task enabled through a handle
// runs its body here -- the assignment takes the forms §8.10 and §8.11 give a
// method over its class's properties, `x = v` for a property x, `this.x`,
// `super.x` and a `new` resolved against a property, through
// ExecFuncBlockingAssign; anywhere else it is ExecBlockingAssignImpl. Defined
// in stmt_exec_class_task.cpp.
StmtResult ExecImmediateBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                       Arena& arena);

ExecTask ExecWait(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecWaitOrder(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecCycleDelay(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecDelay(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecEventControl(const Stmt* stmt, SimContext& ctx, Arena& arena);

// Defined in stmt_exec_control.cpp.
ExecTask ExecBlock(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecIf(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecCase(const Stmt* stmt, SimContext& ctx, Arena& arena);
// §12.5: the body of the item the case statement `stmt` selects, its case
// expression evaluated once and the violations §12.5.3.1 defines for its
// qualifier reported; nullptr where no item and no default matches. Shared
// by the process executor above and the function body's (§13.4), which runs
// the body synchronously (stmt_exec_control.cpp).
const Stmt* SelectCaseBody(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecFor(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecForeach(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecWhile(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecForever(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecRepeat(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecDoWhile(const Stmt* stmt, SimContext& ctx, Arena& arena);

// §16.3 immediate assertion, including its deferred forms (defined in
// stmt_exec_deferred.cpp); reached from the statement dispatcher.
ExecTask ExecImmediateAssert(const Stmt* stmt, SimContext& ctx, Arena& arena);
// §16.17: the expect statement, which blocks the process until the single
// evaluation of its property it starts at the next clocking event succeeds
// or fails, and runs its action block after the Observed region that
// concluded it (expect_statement.cpp).
ExecTask ExecExpect(const Stmt* stmt, SimContext& ctx, Arena& arena);

}  // namespace delta
