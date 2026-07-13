#pragma once

#include <cstdint>

#include "simulator/exec_task.h"

namespace delta {

struct Stmt;
struct Logic4Vec;
class SimContext;
class Arena;

// Defined in stmt_exec_control.cpp. Applies the §9.4.1 delay-control value
// rules (unknown/high-impedance delay reads as zero; a negative delay is
// reinterpreted as a two's-complement unsigned integer the width of a time
// variable) to a delay expression's evaluated value. Shared so the
// intra-assignment delay of a blocking assignment (§10.4.1) normalizes its
// delay the same way a standalone delay-control statement does.
uint64_t DelayTicksFromValue(const Logic4Vec& val);

// Defined in stmt_exec_control.cpp. Turns a delay expression's evaluated value
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
