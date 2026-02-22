// §12.5.1: Case statement with do-not-cares

#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

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

using namespace delta;

// Helper fixture providing scheduler, arena, diag, and sim context.
struct StmtFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag, /*seed=*/42};
};

// Helper to create a simple identifier expression.
Expr *MakeIdent(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// Helper to create an integer literal expression.
Expr *MakeIntLit(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

// Helper to create a blocking assignment statement: lhs = rhs_val.
Stmt *MakeBlockAssign(Arena &arena, std::string_view lhs_name,
                      uint64_t rhs_val) {
  auto *s = arena.Create<Stmt>();
  s->kind = StmtKind::kBlockingAssign;
  s->lhs = MakeIdent(arena, lhs_name);
  s->rhs = MakeIntLit(arena, rhs_val);
  return s;
}

// Driver coroutine that co_awaits an ExecTask and stores its result.
struct DriverResult {
  StmtResult value = StmtResult::kDone;
};

SimCoroutine DriverCoroutine(const Stmt *stmt, SimContext &ctx, Arena &arena,
                             DriverResult *out) {
  out->value = co_await ExecStmt(stmt, ctx, arena);
}

// Helper to run ExecStmt synchronously (for non-suspending statements).
// Creates a wrapper coroutine, resumes it, and returns the result.
StmtResult RunStmt(const Stmt *stmt, SimContext &ctx, Arena &arena) {
  DriverResult result;
  auto coro = DriverCoroutine(stmt, ctx, arena, &result);
  coro.Resume();
  return result.value;
}
namespace {

// =============================================================================
// 8. CaseX (casex matching)
// =============================================================================
TEST(StmtExec, CasexMatchesIgnoringXZ) {
  StmtFixture f;
  auto *result_var = f.ctx.CreateVariable("cx", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // casex (selector)
  //   2'b1x : cx = 1;    // pattern with X bit
  //   default: cx = 99;
  // endcase
  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasex;
  // Selector: 2'b10 => value 2
  stmt->condition = MakeIntLit(f.arena, 2);

  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 2));  // matches 2 (0b10)
  item1.body = MakeBlockAssign(f.arena, "cx", 1);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "cx", 99);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 1u);
}

TEST(StmtExec, CasexNoMatchFallsToDefault) {
  StmtFixture f;
  auto *result_var = f.ctx.CreateVariable("cxd", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasex;
  stmt->condition = MakeIntLit(f.arena, 5);

  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 10));
  item1.body = MakeBlockAssign(f.arena, "cxd", 1);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "cxd", 99);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 99u);
}

// =============================================================================
// 9. CaseZ (casez matching)
// =============================================================================
TEST(StmtExec, CasezExactMatchWorks) {
  StmtFixture f;
  auto *result_var = f.ctx.CreateVariable("cz", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasez;
  stmt->condition = MakeIntLit(f.arena, 3);

  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 3));
  item1.body = MakeBlockAssign(f.arena, "cz", 42);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "cz", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 42u);
}

TEST(StmtExec, CasezNoMatchFallsToDefault) {
  StmtFixture f;
  auto *result_var = f.ctx.CreateVariable("czd", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasez;
  stmt->condition = MakeIntLit(f.arena, 7);

  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 3));
  item1.body = MakeBlockAssign(f.arena, "czd", 1);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "czd", 55);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 55u);
}

// =============================================================================
// 22. Casex with X/Z bits in selector
// =============================================================================
TEST(StmtExec, CasexWithXZInSelector) {
  StmtFixture f;
  auto *result_var = f.ctx.CreateVariable("cxz", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Create a variable with X bits (bval != 0).
  auto *sel_var = f.ctx.CreateVariable("sel_xz", 8);
  sel_var->value = MakeLogic4Vec(f.arena, 8);
  sel_var->value.words[0].aval = 0x02;  // Pattern: 0b10 in lower bits
  sel_var->value.words[0].bval = 0x01;  // LSB is X

  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasex;
  stmt->condition = MakeIdent(f.arena, "sel_xz");

  // Pattern: exact value 2 (0b10) -- should match because casex ignores X.
  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 2));
  item1.body = MakeBlockAssign(f.arena, "cxz", 42);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "cxz", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 42u);
}

// =============================================================================
// 23. Casez with Z bits in selector
// =============================================================================
TEST(StmtExec, CasezWithZInSelector) {
  StmtFixture f;
  auto *result_var = f.ctx.CreateVariable("czz", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Create a variable with Z bit: aval=1,bval=1 => Z.
  auto *sel_var = f.ctx.CreateVariable("sel_z", 8);
  sel_var->value = MakeLogic4Vec(f.arena, 8);
  sel_var->value.words[0].aval = 0x03;  // 0b11
  sel_var->value.words[0].bval = 0x01;  // LSB is Z (aval=1,bval=1)

  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasez;
  stmt->condition = MakeIdent(f.arena, "sel_z");

  // Pattern: 2 (0b10) -- should match because casez treats Z as don't-care.
  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 2));
  item1.body = MakeBlockAssign(f.arena, "czz", 55);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "czz", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 55u);
}

}  // namespace
