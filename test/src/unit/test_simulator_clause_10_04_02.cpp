// §10.4.2: Nonblocking procedural assignments

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// § variable_lvalue — nonblocking assignment
TEST(SimA85, VarLvalueNonblocking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x <= 8'h99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x99u);
}

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
