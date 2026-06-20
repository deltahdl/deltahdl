#pragma once

#include <cstdint>

#include "simulator/exec_task.h"
#include "simulator/stmt_result.h"

namespace delta {

struct Stmt;
class SimContext;
class Arena;
enum class StmtKind : uint8_t;

ExecTask ExecStmt(const Stmt* stmt, SimContext& ctx, Arena& arena);

bool IsTimeControlStatement(StmtKind kind);

}  // namespace delta
