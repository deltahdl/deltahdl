// §9.3.1: Sequential blocks

#include "simulator/lowerer.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

// Sim test fixture
namespace {

// =============================================================================
// A.6.3 Parallel and sequential blocks — Simulation
// =============================================================================
// ---------------------------------------------------------------------------
// Simulation: §9.3.1 sequential block execution order
// ---------------------------------------------------------------------------
// Sequential statements execute in order (second overrides first)
TEST(SimA603, SeqBlockExecutionOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// Sequential block: value from first assignment used in second
TEST(SimA603, SeqBlockValuePropagation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    b = a + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
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
// 2. §4.2 Sequential ordering within a begin-end block (§4.6 guarantee).
//    Statements execute in source order within a single process.
// ---------------------------------------------------------------------------
TEST(SimCh4, SequentialWithinBeginEnd) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    x = 8'd2;\n"
      "    x = 8'd3;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 3u);
}

}  // namespace
