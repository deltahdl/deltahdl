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
// 26. Blocking assignment to member-access LHS (§7.2 / §10.3)
// =============================================================================
TEST(StmtExec, BlockingAssignMemberAccess) {
  StmtFixture f;
  // Create variable "s.a" to represent a struct member.
  auto* var = f.ctx.CreateVariable("s.a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // s.a = 42;
  auto* mem = f.arena.Create<Expr>();
  mem->kind = ExprKind::kMemberAccess;
  mem->lhs = MakeId(f.arena, "s");
  mem->rhs = MakeId(f.arena, "a");

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kBlockingAssign;
  stmt->lhs = mem;
  stmt->rhs = MakeInt(f.arena, 42);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

}  // namespace
