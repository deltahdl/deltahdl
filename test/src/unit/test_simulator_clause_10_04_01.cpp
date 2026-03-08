// Non-LRM tests

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_stmt_exec.h"
#include "simulator/compiled_sim.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SimA85, VarLvalueMultiDimArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  initial begin mem[0] = 8'h00; mem[2] = 8'hAB; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("mem[2]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(SimCh4, BlockingOverwriteInOrder) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd100;\n"
      "    x = 8'd200;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 200u);
}

TEST(CompiledSim, ExecuteBlockingAssign) {
  CompiledSimFixture f;
  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = "x";
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kIntegerLiteral;
  rhs->int_val = 42;
  auto* assign = f.arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->lhs = lhs;
  assign->rhs = rhs;

  auto* block = f.arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(assign);

  auto compiled = ProcessCompiler::Compile(1, block);
  EXPECT_TRUE(compiled.IsValid());
  compiled.Execute(f.ctx);
  EXPECT_EQ(x_var->value.ToUint64(), 42u);
}

TEST(StmtExec, BlockingAssignBitSelect) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("bs", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "bs");
  sel->index = MakeInt(f.arena, 3);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kBlockingAssign;
  stmt->lhs = sel;
  stmt->rhs = MakeInt(f.arena, 1);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0x08u);
}

TEST(StmtExec, BlockingAssignPartSelect) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("ps", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0x0F);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "ps");
  sel->index = MakeInt(f.arena, 7);
  sel->index_end = MakeInt(f.arena, 4);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kBlockingAssign;
  stmt->lhs = sel;
  stmt->rhs = MakeInt(f.arena, 0xA);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0xAFu);
}

TEST(StmtExec, BlockingAssignMemberAccess) {
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

TEST(SimCh10a, BlockingIntraAssignDelay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'd42;\n"
      "    a = #5 b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 42u);
}

TEST(SimCh10a, BlockingIntraAssignDelayBlocksFlow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    b = 8'd10;\n"
      "    a = #5 b;\n"
      "    c = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 10u);
  EXPECT_EQ(c->value.ToUint64(), 99u);
}

TEST(SimCh10a, BlockingIntraAssignDelayCapturesRHS) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'd10;\n"
      "    a = #5 b;\n"
      "  end\n"
      "  initial begin\n"
      "    #2 b = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);

  EXPECT_EQ(a->value.ToUint64(), 10u);
}

}  // namespace
