// §10.4.1: Blocking procedural assignments

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// § variable_lvalue — part select blocking assignment
TEST(SimA85, VarLvaluePartSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'h00; x[7:4] = 4'hF; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xF0u);
}

// § variable_lvalue — concatenation LHS blocking assignment
TEST(SimA85, VarLvalueConcatenation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  initial {a, b} = 8'hA5;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0xAu}, {"b", 0x5u}});
}

// § variable_lvalue — multi-dimensional array element
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

// ===========================================================================
// §4.2 Execution of a hardware model and its verification environment
//
// LRM §4.2 establishes the fundamental execution model:
//   - SystemVerilog is a parallel programming language.
//   - Certain constructs execute as parallel blocks or processes.
//   - Understanding guaranteed vs. indeterminate execution order is key.
//   - Semantics are defined for simulation.
//
// These tests verify the simulation-level behaviour of the concepts
// introduced in §4.2, covering parallel process execution, sequential
// ordering within processes, and interaction between concurrent elements.
// ===========================================================================

// ---------------------------------------------------------------------------
// 12. §4.2 Guaranteed ordering: later blocking assignments overwrite earlier
//     ones in the same begin-end block.
// ---------------------------------------------------------------------------
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

  // Build AST: x = 42
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
