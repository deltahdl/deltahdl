#pragma once

#include "simulator/exec_task.h"

namespace delta {

struct Stmt;
class SimContext;
class Arena;

// Statement executors split out of stmt_exec.cpp into sibling translation
// units. The dispatcher in stmt_exec.cpp calls these by name, so they have
// external linkage and are declared here rather than as file-local statics.

// Defined in stmt_exec_randsequence.cpp.
ExecTask ExecRandcase(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecRandsequence(const Stmt* stmt, SimContext& ctx, Arena& arena);

// Defined in stmt_exec_wait.cpp.
ExecTask ExecWait(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecWaitOrder(const Stmt* stmt, SimContext& ctx, Arena& arena);

// Defined in stmt_exec_control.cpp.
ExecTask ExecBlock(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecIf(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecCase(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecFor(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecForeach(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecWhile(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecForever(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecRepeat(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecDoWhile(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecCycleDelay(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecDelay(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecEventControl(const Stmt* stmt, SimContext& ctx, Arena& arena);

}  // namespace delta
