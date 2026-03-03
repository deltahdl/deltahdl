// Non-LRM tests

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

namespace {

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
  force_stmt->lhs = MakeId(f.arena, "fra");
  force_stmt->rhs = MakeInt(f.arena, 50);
  RunStmt(force_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 50u);
  EXPECT_TRUE(var->is_forced);

  // Release fra;
  auto* release_stmt = f.arena.Create<Stmt>();
  release_stmt->kind = StmtKind::kRelease;
  release_stmt->lhs = MakeId(f.arena, "fra");
  RunStmt(release_stmt, f.ctx, f.arena);
  EXPECT_FALSE(var->is_forced);

  // Assign fra = 75 (normal blocking)
  auto* assign_stmt = MakeBlockAssign(f.arena, "fra", 75);
  RunStmt(assign_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 75u);
}

}  // namespace
