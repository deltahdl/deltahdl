#pragma once

#include "simulation/exec_task.h"
#include "simulation/stmt_result.h"

namespace delta {

struct Stmt;
class SimContext;
class Arena;

ExecTask ExecStmt(const Stmt* stmt, SimContext& ctx, Arena& arena);

}  // namespace delta
