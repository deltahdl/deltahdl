#pragma once

#include <cstdint>
#include <string_view>

#include "common/arena.h"
#include "parser/ast.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"

#include "builders_ast.h"

using namespace delta;

inline Stmt* MakeBlockAssign(Arena& arena, std::string_view lhs_name,
                             uint64_t rhs_val) {
  return MakeAssign(arena, lhs_name, MakeInt(arena, rhs_val));
}

struct DriverResult {
  StmtResult value = StmtResult::kDone;
};

inline SimCoroutine DriverCoroutine(const Stmt* stmt, SimContext& ctx,
                                    Arena& arena, DriverResult* out) {
  out->value = co_await ExecStmt(stmt, ctx, arena);
}

inline StmtResult RunStmt(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  DriverResult result;
  auto coro = DriverCoroutine(stmt, ctx, arena, &result);
  coro.Resume();
  return result.value;
}
