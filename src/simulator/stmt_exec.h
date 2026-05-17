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

// §4.7 ¶1 sentence 3: "Time control statements are the # expression and
// @ expression constructs (see 9.4)." Returns true for StmtKind::kDelay
// (the # expression) and StmtKind::kEventControl (the @ expression);
// false for every other statement kind. Production callers consult
// this classifier when deciding whether a procedural statement is one
// the §4.7 "do not have to be executed as one event" latitude applies
// to.
bool IsTimeControlStatement(StmtKind kind);

}  // namespace delta
