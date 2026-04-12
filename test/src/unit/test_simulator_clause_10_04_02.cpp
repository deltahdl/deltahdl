
#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_stmt_exec.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NonblockingAssignSim, BitSelect) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("nb", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "nb");
  sel->index = MakeInt(f.arena, 5);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kNonblockingAssign;
  stmt->lhs = sel;
  stmt->rhs = MakeInt(f.arena, 1);

  RunStmt(stmt, f.ctx, f.arena);

  f.scheduler.Run();
  EXPECT_EQ(var->value.ToUint64(), 0x20u);
}

TEST(NonblockingAssignSim, BlockingImmediateNonblockingDeferred) {
  auto b_val = RunAndGet(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    b <= a;\n"
      "    a = 99;\n"
      "  end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(b_val, 10u);
}

TEST(NonblockingAssignSim, LhsIndexEvaluatedAtScheduleTime) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  int idx;\n"
      "  initial begin\n"
      "    mem[0] = 0;\n"
      "    mem[1] = 0;\n"
      "    idx = 0;\n"
      "    mem[idx] <= 8'hAA;\n"
      "    idx = 1;\n"
      "  end\n"
      "endmodule\n",
      "mem[0]");
  EXPECT_EQ(val, 0xAAu);
}

TEST(NonblockingAssignSim, RhsEvaluatedAtScheduleTime) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 3;\n"
      "    b = 4;\n"
      "    result <= a + b;\n"
      "    a = 100;\n"
      "    b = 200;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 7u);
}

}  // namespace
