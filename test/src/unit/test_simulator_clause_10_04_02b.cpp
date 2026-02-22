// §10.4.2: Nonblocking procedural assignments

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/awaiters.h"
#include "simulation/exec_task.h"
#include "simulation/process.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/stmt_exec.h"
#include "simulation/stmt_result.h"
#include "simulation/variable.h"
#include <cstdint>
#include <gtest/gtest.h>
#include <string_view>

using namespace delta;

struct StmtFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag, /*seed=*/42};
};

Expr *MakeIdent(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

Expr *MakeIntLit(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

struct DriverResult {
  StmtResult value = StmtResult::kDone;
};

SimCoroutine DriverCoroutine(const Stmt *stmt, SimContext &ctx, Arena &arena,
                             DriverResult *out) {
  out->value = co_await ExecStmt(stmt, ctx, arena);
}

StmtResult RunStmt(const Stmt *stmt, SimContext &ctx, Arena &arena) {
  DriverResult result;
  auto coro = DriverCoroutine(stmt, ctx, arena, &result);
  coro.Resume();
  return result.value;
}
namespace {

// =============================================================================
// 27. Nonblocking assignment to bit-select LHS (§10.4.2)
// =============================================================================
TEST(StmtExec, NonblockingAssignBitSelect) {
  StmtFixture f;
  auto *var = f.ctx.CreateVariable("nb", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0);

  // nb[5] <= 1;
  auto *sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeIdent(f.arena, "nb");
  sel->index = MakeIntLit(f.arena, 5);

  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kNonblockingAssign;
  stmt->lhs = sel;
  stmt->rhs = MakeIntLit(f.arena, 1);

  RunStmt(stmt, f.ctx, f.arena);
  // NBA is deferred -- drain the scheduler to apply it.
  f.scheduler.Run();
  EXPECT_EQ(var->value.ToUint64(), 0x20u); // bit 5 set
}

} // namespace
