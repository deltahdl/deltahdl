// §9.4.2: Event control

#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"
#include "builders_ast.h"
#include "helpers_stmt_exec.h"

using namespace delta;

// Helper to create a blocking assignment statement: lhs = rhs_val.

// Driver coroutine that co_awaits an ExecTask and stores its result.

// Helper to run ExecStmt synchronously (for non-suspending statements).
// Creates a wrapper coroutine, resumes it, and returns the result.
namespace {

// =============================================================================
// 13. Wait order (StmtKind::kWaitOrder)
// =============================================================================
TEST(StmtExec, WaitOrderImmediateReturnsKDone) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kWaitOrder;
  stmt->wait_order_events.push_back(MakeId(f.arena, "ev1"));
  stmt->wait_order_events.push_back(MakeId(f.arena, "ev2"));

  // Without actual event infrastructure, WaitOrder returns kDone immediately.
  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

}  // namespace
