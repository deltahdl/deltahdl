#pragma once

#include <cstdint>

#include "common/types.h"
#include "simulator/exec_task.h"

namespace delta {

struct Stmt;
struct Expr;
class SimContext;
struct Variable;
class Arena;
enum class StmtKind : uint8_t;

ExecTask ExecStmt(const Stmt* stmt, SimContext& ctx, Arena& arena);

bool TryExecSystemCallTask(const Expr* expr, SimContext& ctx, Arena& arena);

void SpawnForkJoinNone(const Stmt* stmt, SimContext& ctx, Arena& arena);

const Stmt* ExecImmediateAssertInFunction(const Stmt* stmt, SimContext& ctx,
                                          Arena& arena);

void ExecEventTriggerInFunction(const Stmt* stmt, SimContext& ctx,
                                Arena& arena);

void TriggerEvent(Variable* var, SimContext& ctx);

void TriggerEventIn(Variable* var, SimContext& ctx, Region region);

bool IsTimeControlStatement(StmtKind kind);

}  // namespace delta
