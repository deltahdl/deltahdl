#pragma once

#include <cstdint>

#include "simulator/exec_task.h"
#include "simulator/stmt_result.h"

namespace delta {

struct Stmt;
struct Expr;
class SimContext;
class Arena;
enum class StmtKind : uint8_t;

ExecTask ExecStmt(const Stmt* stmt, SimContext& ctx, Arena& arena);

// Runs `expr` as the task form of the system call it names, and reports whether
// it named one. §6.24.2 and §20.17.2 give $cast and $stacktrace a task form
// whose behaviour differs from the function form that evaluating the expression
// produces, so an executor that only evaluates a statement's expression gives
// the source the wrong one of the two. Every executor of an expression
// statement calls this first and evaluates the expression only when it returns
// false, so a system call whose task form is added later is handled at all of
// them at once.
bool TryExecSystemCallTask(const Expr* expr, SimContext& ctx, Arena& arena);

// §13.4.4: spawn the background processes of a fork...join_none reached from a
// synchronous (non-coroutine) executor such as a function body. No-op unless
// the fork's join kind is join_none.
void SpawnForkJoinNone(const Stmt* stmt, SimContext& ctx, Arena& arena);

// §16.4.5: evaluate and schedule a deferred immediate assertion reached from a
// function body. The report is queued against the calling process, so a
// function shared by several processes produces an independent report per
// process. Intended for the synchronous function-body executor, which cannot
// co_await; only the deferred (#0 / final) forms are handled.
void ExecDeferredImmediateAssertInFunction(const Stmt* stmt, SimContext& ctx,
                                           Arena& arena);

bool IsTimeControlStatement(StmtKind kind);

}  // namespace delta
