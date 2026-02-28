// §9.6.2: Disable statement

#include <cstdint>
#include <string_view>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

using namespace delta;

// Helper to create a blocking assignment statement: lhs = rhs_val.

// Driver coroutine that co_awaits an ExecTask and stores its result.

// Helper to run ExecStmt synchronously (for non-suspending statements).
// Creates a wrapper coroutine, resumes it, and returns the result.
namespace {

// =============================================================================
// 3. Disable (StmtKind::kDisable)
// =============================================================================
TEST(StmtExec, DisableReturnsKDone) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kDisable;
  stmt->expr = MakeId(f.arena, "myblock");

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

}  // namespace
