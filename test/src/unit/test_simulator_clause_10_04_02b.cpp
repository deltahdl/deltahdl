// §10.4.2: Nonblocking procedural assignments

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

namespace {

// =============================================================================
// 27. Nonblocking assignment to bit-select LHS (§10.4.2)
// =============================================================================
TEST(StmtExec, NonblockingAssignBitSelect) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("nb", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0);

  // nb[5] <= 1;
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "nb");
  sel->index = MakeInt(f.arena, 5);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kNonblockingAssign;
  stmt->lhs = sel;
  stmt->rhs = MakeInt(f.arena, 1);

  RunStmt(stmt, f.ctx, f.arena);
  // NBA is deferred -- drain the scheduler to apply it.
  f.scheduler.Run();
  EXPECT_EQ(var->value.ToUint64(), 0x20u);  // bit 5 set
}

}  // namespace
