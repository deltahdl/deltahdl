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

}  // namespace
