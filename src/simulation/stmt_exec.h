#pragma once

#include <cstdint>

namespace delta {

struct Stmt;
class SimContext;
class Arena;

enum class StmtResult : uint8_t {
  kDone,
  kSuspendDelay,
  kSuspendEvent,
  kBreak,
  kContinue,
  kReturn,
};

StmtResult ExecStmt(const Stmt* stmt, SimContext& ctx, Arena& arena);

}  // namespace delta
