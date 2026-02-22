// §10.4.1: Blocking procedural assignments

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
// 24. Blocking assignment to bit-select LHS (§7.4 / §10.3)
// =============================================================================
TEST(StmtExec, BlockingAssignBitSelect) {
  StmtFixture f;
  auto *var = f.ctx.CreateVariable("bs", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0);

  // bs[3] = 1;
  auto *sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeIdent(f.arena, "bs");
  sel->index = MakeIntLit(f.arena, 3);

  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kBlockingAssign;
  stmt->lhs = sel;
  stmt->rhs = MakeIntLit(f.arena, 1);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0x08u); // bit 3 set
}

// =============================================================================
// 25. Blocking assignment to part-select LHS (§7.4.5 / §10.3)
// =============================================================================
TEST(StmtExec, BlockingAssignPartSelect) {
  StmtFixture f;
  auto *var = f.ctx.CreateVariable("ps", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0x0F);

  // ps[7:4] = 4'hA;
  auto *sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeIdent(f.arena, "ps");
  sel->index = MakeIntLit(f.arena, 7);
  sel->index_end = MakeIntLit(f.arena, 4);

  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kBlockingAssign;
  stmt->lhs = sel;
  stmt->rhs = MakeIntLit(f.arena, 0xA);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0xAFu); // upper nibble = A, lower = F
}

// =============================================================================
// 26. Blocking assignment to member-access LHS (§7.2 / §10.3)
// =============================================================================
TEST(StmtExec, BlockingAssignMemberAccess) {
  StmtFixture f;
  // Create variable "s.a" to represent a struct member.
  auto *var = f.ctx.CreateVariable("s.a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // s.a = 42;
  auto *mem = f.arena.Create<Expr>();
  mem->kind = ExprKind::kMemberAccess;
  mem->lhs = MakeIdent(f.arena, "s");
  mem->rhs = MakeIdent(f.arena, "a");

  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kBlockingAssign;
  stmt->lhs = mem;
  stmt->rhs = MakeIntLit(f.arena, 42);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

} // namespace
