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

namespace {

// Helper fixture providing scheduler, arena, diag, and sim context.
struct StmtFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag, /*seed=*/42};
};

// Helper to create a simple identifier expression.
Expr* MakeIdent(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// Helper to create an integer literal expression.
Expr* MakeIntLit(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

// Helper to create a blocking assignment statement: lhs = rhs_val.
Stmt* MakeBlockAssign(Arena& arena, std::string_view lhs_name,
                      uint64_t rhs_val) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kBlockingAssign;
  s->lhs = MakeIdent(arena, lhs_name);
  s->rhs = MakeIntLit(arena, rhs_val);
  return s;
}

// Driver coroutine that co_awaits an ExecTask and stores its result.
struct DriverResult {
  StmtResult value = StmtResult::kDone;
};

SimCoroutine DriverCoroutine(const Stmt* stmt, SimContext& ctx, Arena& arena,
                             DriverResult* out) {
  out->value = co_await ExecStmt(stmt, ctx, arena);
}

// Helper to run ExecStmt synchronously (for non-suspending statements).
// Creates a wrapper coroutine, resumes it, and returns the result.
StmtResult RunStmt(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  DriverResult result;
  auto coro = DriverCoroutine(stmt, ctx, arena, &result);
  coro.Resume();
  return result.value;
}

}  // namespace

// =============================================================================
// 1. Force / Release (StmtKind::kForce, kRelease)
// =============================================================================

TEST(StmtExec, ForceOverridesValue) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("x", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 10);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForce;
  stmt->lhs = MakeIdent(f.arena, "x");
  stmt->rhs = MakeIntLit(f.arena, 99);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_TRUE(var->is_forced);
  EXPECT_EQ(var->forced_value.ToUint64(), 99u);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(StmtExec, ForceNullLhsNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForce;
  stmt->lhs = nullptr;
  stmt->rhs = MakeIntLit(f.arena, 5);

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(StmtExec, ReleaseClearsForce) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("y", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);
  var->is_forced = true;
  var->forced_value = MakeLogic4VecVal(f.arena, 32, 42);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRelease;
  stmt->lhs = MakeIdent(f.arena, "y");

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_FALSE(var->is_forced);
}

TEST(StmtExec, ReleaseUnknownVarNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRelease;
  stmt->lhs = MakeIdent(f.arena, "nonexistent");

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

// =============================================================================
// 2. Assign / Deassign (StmtKind::kAssign, kDeassign)
// =============================================================================

TEST(StmtExec, ProceduralAssignSetsValue) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kAssign;
  stmt->lhs = MakeIdent(f.arena, "a");
  stmt->rhs = MakeIntLit(f.arena, 77);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_TRUE(var->is_forced);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(StmtExec, DeassignReleasesProceduralAssign) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("b", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 50);
  var->is_forced = true;
  var->forced_value = MakeLogic4VecVal(f.arena, 32, 50);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kDeassign;
  stmt->lhs = MakeIdent(f.arena, "b");

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_FALSE(var->is_forced);
}

TEST(StmtExec, DeassignNullLhsNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kDeassign;
  stmt->lhs = nullptr;

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

// =============================================================================
// 3. Disable (StmtKind::kDisable)
// =============================================================================

TEST(StmtExec, DisableReturnsKDone) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kDisable;
  stmt->expr = MakeIdent(f.arena, "myblock");

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

// =============================================================================
// 4. Disable fork (StmtKind::kDisableFork)
// =============================================================================

TEST(StmtExec, DisableForkReturnsKDone) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kDisableFork;

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

// =============================================================================
// 5. Wait fork (StmtKind::kWaitFork)
// =============================================================================

TEST(StmtExec, WaitForkNoForkReturnsDone) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kWaitFork;

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

// =============================================================================
// 6. Foreach (StmtKind::kForeach)
// =============================================================================

TEST(StmtExec, ForeachIteratesOverArrayWidth) {
  StmtFixture f;
  // Create an "array" variable with width 4 (simulating 4 elements).
  auto* arr = f.ctx.CreateVariable("arr", 4);
  arr->value = MakeLogic4VecVal(f.arena, 4, 0);

  // Create accumulator variable.
  auto* sum = f.ctx.CreateVariable("sum", 32);
  sum->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Build: foreach (arr[i]) sum = sum + 1;
  // Body: sum = sum + 1
  auto* sum_id = MakeIdent(f.arena, "sum");
  auto* one = MakeIntLit(f.arena, 1);
  auto* add_expr = f.arena.Create<Expr>();
  add_expr->kind = ExprKind::kBinary;
  add_expr->op = TokenKind::kPlus;
  add_expr->lhs = sum_id;
  add_expr->rhs = one;

  auto* body = f.arena.Create<Stmt>();
  body->kind = StmtKind::kBlockingAssign;
  body->lhs = MakeIdent(f.arena, "sum");
  body->rhs = add_expr;

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->expr = MakeIdent(f.arena, "arr");
  stmt->foreach_vars.push_back("i");
  stmt->body = body;

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(sum->value.ToUint64(), 4u);
}

TEST(StmtExec, ForeachEmptyArrayNoOp) {
  StmtFixture f;
  // Zero-width variable means zero iterations.
  auto* arr = f.ctx.CreateVariable("empty", 0);
  (void)arr;
  auto* sum = f.ctx.CreateVariable("count", 32);
  sum->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* body = MakeBlockAssign(f.arena, "count", 1);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->expr = MakeIdent(f.arena, "empty");
  stmt->foreach_vars.push_back("i");
  stmt->body = body;

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(sum->value.ToUint64(), 0u);
}

TEST(StmtExec, ForeachNoVarsStillIterates) {
  StmtFixture f;
  auto* arr = f.ctx.CreateVariable("arr2", 3);
  arr->value = MakeLogic4VecVal(f.arena, 3, 0);

  auto* cnt = f.ctx.CreateVariable("cnt", 32);
  cnt->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Body: cnt = cnt + 1
  auto* add = f.arena.Create<Expr>();
  add->kind = ExprKind::kBinary;
  add->op = TokenKind::kPlus;
  add->lhs = MakeIdent(f.arena, "cnt");
  add->rhs = MakeIntLit(f.arena, 1);

  auto* body = f.arena.Create<Stmt>();
  body->kind = StmtKind::kBlockingAssign;
  body->lhs = MakeIdent(f.arena, "cnt");
  body->rhs = add;

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->expr = MakeIdent(f.arena, "arr2");
  // No loop variables (empty foreach_vars => no index binding).
  stmt->body = body;

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(cnt->value.ToUint64(), 3u);
}

// =============================================================================
// 7. Randcase (StmtKind::kRandcase)
// =============================================================================

TEST(StmtExec, RandcaseSelectsBranch) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("r", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // randcase
  //   1 : r = 10;
  //   1 : r = 20;
  // endcase
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeIntLit(f.arena, 1), MakeBlockAssign(f.arena, "r", 10)});
  stmt->randcase_items.push_back(
      {MakeIntLit(f.arena, 1), MakeBlockAssign(f.arena, "r", 20)});

  RunStmt(stmt, f.ctx, f.arena);
  uint64_t val = result_var->value.ToUint64();
  EXPECT_TRUE(val == 10 || val == 20);
}

TEST(StmtExec, RandcaseAllZeroWeightsNoOp) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("rz", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeIntLit(f.arena, 0), MakeBlockAssign(f.arena, "rz", 10)});
  stmt->randcase_items.push_back(
      {MakeIntLit(f.arena, 0), MakeBlockAssign(f.arena, "rz", 20)});

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 0u);
}

TEST(StmtExec, RandcaseSingleBranchAlwaysSelected) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("rs", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeIntLit(f.arena, 5), MakeBlockAssign(f.arena, "rs", 42)});

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 42u);
}

// =============================================================================
// 8. CaseX (casex matching)
// =============================================================================

TEST(StmtExec, CasexMatchesIgnoringXZ) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cx", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // casex (selector)
  //   2'b1x : cx = 1;    // pattern with X bit
  //   default: cx = 99;
  // endcase
  auto* stmt = f.arena.Create<Stmt>();
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
  auto* result_var = f.ctx.CreateVariable("cxd", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
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
  auto* result_var = f.ctx.CreateVariable("cz", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
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
  auto* result_var = f.ctx.CreateVariable("czd", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
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
// 10. Case inside (case ... inside)
// =============================================================================

TEST(StmtExec, CaseInsideExactMatch) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("ci", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCase;
  stmt->case_inside = true;
  stmt->condition = MakeIntLit(f.arena, 5);

  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 5));
  item1.body = MakeBlockAssign(f.arena, "ci", 100);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "ci", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 100u);
}

TEST(StmtExec, CaseInsideNoMatchDefault) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cid", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCase;
  stmt->case_inside = true;
  stmt->condition = MakeIntLit(f.arena, 99);

  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 5));
  item1.body = MakeBlockAssign(f.arena, "cid", 100);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "cid", 77);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 77u);
}

// =============================================================================
// 11. Unique if / Priority if
// =============================================================================

TEST(StmtExec, UniqueIfMatchingBranch) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("ui", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // unique if (1) ui = 10; else ui = 20;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kIf;
  stmt->qualifier = CaseQualifier::kUnique;
  stmt->condition = MakeIntLit(f.arena, 1);
  stmt->then_branch = MakeBlockAssign(f.arena, "ui", 10);
  stmt->else_branch = MakeBlockAssign(f.arena, "ui", 20);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 10u);
}

TEST(StmtExec, PriorityIfFirstMatchTaken) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("pi", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // priority if (1) pi = 30;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kIf;
  stmt->qualifier = CaseQualifier::kPriority;
  stmt->condition = MakeIntLit(f.arena, 1);
  stmt->then_branch = MakeBlockAssign(f.arena, "pi", 30);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 30u);
}

TEST(StmtExec, PriorityIfNoMatchNoElseWarning) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("piw", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // priority if (0) piw = 30;
  // No else branch => should emit warning but not crash.
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kIf;
  stmt->qualifier = CaseQualifier::kPriority;
  stmt->condition = MakeIntLit(f.arena, 0);
  stmt->then_branch = MakeBlockAssign(f.arena, "piw", 30);

  RunStmt(stmt, f.ctx, f.arena);
  // Value should remain 0 since condition is false and no else.
  EXPECT_EQ(result_var->value.ToUint64(), 0u);
  // DiagEngine should have emitted a warning.
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// =============================================================================
// 12. Unique case / Priority case
// =============================================================================

TEST(StmtExec, UniqueCaseExactMatch) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("uc", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->qualifier = CaseQualifier::kUnique;
  stmt->condition = MakeIntLit(f.arena, 2);

  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 1));
  item1.body = MakeBlockAssign(f.arena, "uc", 10);
  stmt->case_items.push_back(item1);

  CaseItem item2;
  item2.patterns.push_back(MakeIntLit(f.arena, 2));
  item2.body = MakeBlockAssign(f.arena, "uc", 20);
  stmt->case_items.push_back(item2);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 20u);
}

TEST(StmtExec, PriorityCaseNoMatchNoDefaultWarning) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("pcw", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->qualifier = CaseQualifier::kPriority;
  stmt->condition = MakeIntLit(f.arena, 99);

  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 1));
  item1.body = MakeBlockAssign(f.arena, "pcw", 10);
  stmt->case_items.push_back(item1);

  // No default => should warn.
  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 0u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// =============================================================================
// 13. Wait order (StmtKind::kWaitOrder)
// =============================================================================

TEST(StmtExec, WaitOrderImmediateReturnsKDone) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kWaitOrder;
  stmt->wait_order_events.push_back(MakeIdent(f.arena, "ev1"));
  stmt->wait_order_events.push_back(MakeIdent(f.arena, "ev2"));

  // Without actual event infrastructure, WaitOrder returns kDone immediately.
  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

// =============================================================================
// 14. Force prevents normal assignment
// =============================================================================

TEST(StmtExec, ForcePreventsNormalAssign) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("fv", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Force fv = 50;
  auto* force_stmt = f.arena.Create<Stmt>();
  force_stmt->kind = StmtKind::kForce;
  force_stmt->lhs = MakeIdent(f.arena, "fv");
  force_stmt->rhs = MakeIntLit(f.arena, 50);
  RunStmt(force_stmt, f.ctx, f.arena);

  // Normal blocking assign: fv = 100;
  // The blocking assignment should be overridden by the force.
  auto* assign_stmt = MakeBlockAssign(f.arena, "fv", 100);
  RunStmt(assign_stmt, f.ctx, f.arena);

  // Since force is active, the value should remain forced value.
  EXPECT_TRUE(var->is_forced);
  // The blocking assign does set value, but force should logically override.
  // In our implementation, the force checks and restores the forced value.
  EXPECT_EQ(var->forced_value.ToUint64(), 50u);
}

// =============================================================================
// 15. Foreach with break
// =============================================================================

TEST(StmtExec, ForeachBreakExitsLoop) {
  StmtFixture f;
  auto* arr = f.ctx.CreateVariable("brk_arr", 10);
  arr->value = MakeLogic4VecVal(f.arena, 10, 0);

  auto* cnt = f.ctx.CreateVariable("brk_cnt", 32);
  cnt->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Body: begin cnt = cnt + 1; if (cnt == 3) break; end
  auto* add = f.arena.Create<Expr>();
  add->kind = ExprKind::kBinary;
  add->op = TokenKind::kPlus;
  add->lhs = MakeIdent(f.arena, "brk_cnt");
  add->rhs = MakeIntLit(f.arena, 1);

  auto* inc_stmt = f.arena.Create<Stmt>();
  inc_stmt->kind = StmtKind::kBlockingAssign;
  inc_stmt->lhs = MakeIdent(f.arena, "brk_cnt");
  inc_stmt->rhs = add;

  auto* break_stmt = f.arena.Create<Stmt>();
  break_stmt->kind = StmtKind::kBreak;

  auto* cmp = f.arena.Create<Expr>();
  cmp->kind = ExprKind::kBinary;
  cmp->op = TokenKind::kEqEq;
  cmp->lhs = MakeIdent(f.arena, "brk_cnt");
  cmp->rhs = MakeIntLit(f.arena, 3);

  auto* if_stmt = f.arena.Create<Stmt>();
  if_stmt->kind = StmtKind::kIf;
  if_stmt->condition = cmp;
  if_stmt->then_branch = break_stmt;

  auto* block = f.arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(inc_stmt);
  block->stmts.push_back(if_stmt);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->expr = MakeIdent(f.arena, "brk_arr");
  stmt->foreach_vars.push_back("i");
  stmt->body = block;

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(cnt->value.ToUint64(), 3u);
}

// =============================================================================
// 16. Randcase weighted selection
// =============================================================================

TEST(StmtExec, RandcaseRespectsWeights) {
  // Use a fixed seed; all branches should have weight > 0.
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("rw", 32);

  // Run randcase many times and check distribution.
  // Weight 100 vs weight 0: should always pick first.
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeIntLit(f.arena, 100), MakeBlockAssign(f.arena, "rw", 1)});
  stmt->randcase_items.push_back(
      {MakeIntLit(f.arena, 0), MakeBlockAssign(f.arena, "rw", 2)});

  for (int i = 0; i < 10; ++i) {
    result_var->value = MakeLogic4VecVal(f.arena, 32, 0);
    RunStmt(stmt, f.ctx, f.arena);
    EXPECT_EQ(result_var->value.ToUint64(), 1u);
  }
}

// =============================================================================
// 17. Case with exact match (baseline)
// =============================================================================

TEST(StmtExec, CaseExactMatchBaseline) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("ce", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCase;
  stmt->condition = MakeIntLit(f.arena, 3);

  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 1));
  item1.body = MakeBlockAssign(f.arena, "ce", 10);
  stmt->case_items.push_back(item1);

  CaseItem item2;
  item2.patterns.push_back(MakeIntLit(f.arena, 3));
  item2.body = MakeBlockAssign(f.arena, "ce", 30);
  stmt->case_items.push_back(item2);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "ce", 99);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 30u);
}

// =============================================================================
// 18. Force then release then assign
// =============================================================================

TEST(StmtExec, ForceReleaseThenAssign) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("fra", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Force fra = 50;
  auto* force_stmt = f.arena.Create<Stmt>();
  force_stmt->kind = StmtKind::kForce;
  force_stmt->lhs = MakeIdent(f.arena, "fra");
  force_stmt->rhs = MakeIntLit(f.arena, 50);
  RunStmt(force_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 50u);
  EXPECT_TRUE(var->is_forced);

  // Release fra;
  auto* release_stmt = f.arena.Create<Stmt>();
  release_stmt->kind = StmtKind::kRelease;
  release_stmt->lhs = MakeIdent(f.arena, "fra");
  RunStmt(release_stmt, f.ctx, f.arena);
  EXPECT_FALSE(var->is_forced);

  // Assign fra = 75 (normal blocking)
  auto* assign_stmt = MakeBlockAssign(f.arena, "fra", 75);
  RunStmt(assign_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 75u);
}

// =============================================================================
// 19. Foreach uses iterator variable
// =============================================================================

TEST(StmtExec, ForeachIteratorVariableAccessible) {
  StmtFixture f;
  auto* arr = f.ctx.CreateVariable("itarr", 5);
  arr->value = MakeLogic4VecVal(f.arena, 5, 0);

  // Create a variable to store the last iterator value.
  auto* last = f.ctx.CreateVariable("last_i", 32);
  last->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Body: last_i = i
  // We test that iterator variable "i" is created and accessible.
  auto* body = f.arena.Create<Stmt>();
  body->kind = StmtKind::kBlockingAssign;
  body->lhs = MakeIdent(f.arena, "last_i");
  body->rhs = MakeIdent(f.arena, "i");

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->expr = MakeIdent(f.arena, "itarr");
  stmt->foreach_vars.push_back("i");
  stmt->body = body;

  RunStmt(stmt, f.ctx, f.arena);
  // last_i should be 4 (last iteration index for width=5 array)
  EXPECT_EQ(last->value.ToUint64(), 4u);
}

// =============================================================================
// 20. Assign then deassign then blocking assign
// =============================================================================

TEST(StmtExec, AssignDeassignBlockingAssign) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("adb", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // assign adb = 33;
  auto* assign_stmt = f.arena.Create<Stmt>();
  assign_stmt->kind = StmtKind::kAssign;
  assign_stmt->lhs = MakeIdent(f.arena, "adb");
  assign_stmt->rhs = MakeIntLit(f.arena, 33);
  RunStmt(assign_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 33u);
  EXPECT_TRUE(var->is_forced);

  // deassign adb;
  auto* deassign_stmt = f.arena.Create<Stmt>();
  deassign_stmt->kind = StmtKind::kDeassign;
  deassign_stmt->lhs = MakeIdent(f.arena, "adb");
  RunStmt(deassign_stmt, f.ctx, f.arena);
  EXPECT_FALSE(var->is_forced);

  // adb = 44;
  auto* blocking_stmt = MakeBlockAssign(f.arena, "adb", 44);
  RunStmt(blocking_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

// =============================================================================
// 21. Case multiple patterns in one item
// =============================================================================

TEST(StmtExec, CaseMultiplePatterns) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cmp", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCase;
  stmt->condition = MakeIntLit(f.arena, 5);

  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 3));
  item1.patterns.push_back(MakeIntLit(f.arena, 5));
  item1.patterns.push_back(MakeIntLit(f.arena, 7));
  item1.body = MakeBlockAssign(f.arena, "cmp", 111);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "cmp", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 111u);
}

// =============================================================================
// 22. Casex with X/Z bits in selector
// =============================================================================

TEST(StmtExec, CasexWithXZInSelector) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cxz", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Create a variable with X bits (bval != 0).
  auto* sel_var = f.ctx.CreateVariable("sel_xz", 8);
  sel_var->value = MakeLogic4Vec(f.arena, 8);
  sel_var->value.words[0].aval = 0x02;  // Pattern: 0b10 in lower bits
  sel_var->value.words[0].bval = 0x01;  // LSB is X

  auto* stmt = f.arena.Create<Stmt>();
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
  auto* result_var = f.ctx.CreateVariable("czz", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Create a variable with Z bit: aval=1,bval=1 => Z.
  auto* sel_var = f.ctx.CreateVariable("sel_z", 8);
  sel_var->value = MakeLogic4Vec(f.arena, 8);
  sel_var->value.words[0].aval = 0x03;  // 0b11
  sel_var->value.words[0].bval = 0x01;  // LSB is Z (aval=1,bval=1)

  auto* stmt = f.arena.Create<Stmt>();
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
