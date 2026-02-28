// §4.2: Execution of a hardware model and its verification environment

#include "simulator/lowerer.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

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

namespace {

// ---------------------------------------------------------------------------
// 3. §4.2 Parallel processes with sequential bodies: each process has its
//    own sequential flow, but processes run concurrently.
// ---------------------------------------------------------------------------
TEST(SimCh4, ParallelProcessesSequentialBodies) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    a = a + 8'd5;\n"
      "  end\n"
      "  initial begin\n"
      "    b = 8'd20;\n"
      "    b = b + 8'd7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 15u);
  EXPECT_EQ(vb->value.ToUint64(), 27u);
}

// ---------------------------------------------------------------------------
// 11. §4.2 Parallel processes: three independent initial blocks all complete.
// ---------------------------------------------------------------------------
TEST(SimCh4, ThreeParallelInitialBlocks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd11;\n"
      "  initial b = 8'd22;\n"
      "  initial c = 8'd33;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 11u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 22u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 33u);
}

// ---------------------------------------------------------------------------
// 18. §4.2 Parallel execution with conditional logic: two processes with
//     independent if-else blocks.
// ---------------------------------------------------------------------------
TEST(SimCh4, ParallelConditionalLogic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    if (1) a = 8'd1;\n"
      "    else a = 8'd0;\n"
      "  end\n"
      "  initial begin\n"
      "    if (0) b = 8'd1;\n"
      "    else b = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0u);
}

// ---------------------------------------------------------------------------
// 23. §4.2 Processes at varying abstraction levels: initial (behavioral),
//     assign (dataflow), and always_comb (combinational) all cooperate.
// ---------------------------------------------------------------------------
TEST(SimCh4, ThreeAbstractionLevels) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd3;\n"
      "  assign b = a << 1;\n"
      "  always_comb c = b + 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // a=3, b=6 (shift left), c=7
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 7u);
}

}  // namespace
