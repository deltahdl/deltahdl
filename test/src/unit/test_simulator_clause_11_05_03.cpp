// §11.5.3

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_stmt_exec.h"
#include "simulator/compiled_sim.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(BlockingAssignMemberAccess, BlockingAssignMemberAccess) {
  StmtFixture f;

  auto* var = f.ctx.CreateVariable("s.a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

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
