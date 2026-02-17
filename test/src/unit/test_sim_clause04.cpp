#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

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

struct SimCh4Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh4Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet(const std::string& src, const char* var_name) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0;
  return var->value.ToUint64();
}

// ---------------------------------------------------------------------------
// 1. §4.2 Parallel processes: Multiple initial blocks execute concurrently.
//    Both blocks write to separate variables; both should complete.
// ---------------------------------------------------------------------------
TEST(SimCh4, ParallelInitialBlocks) {
  auto a = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = 8'd42;\n"
      "  initial b = 8'd99;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(a, 42u);
}

TEST(SimCh4, ParallelInitialBlocksBothComplete) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = 8'd42;\n"
      "  initial b = 8'd99;\n"
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
  EXPECT_EQ(va->value.ToUint64(), 42u);
  EXPECT_EQ(vb->value.ToUint64(), 99u);
}

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

// ---------------------------------------------------------------------------
// 3. §4.2 Parallel processes with sequential bodies: each process has its
//    own sequential flow, but processes run concurrently.
// ---------------------------------------------------------------------------
TEST(SimCh4, ParallelProcessesSequentialBodies) {
  SimCh4Fixture f;
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
// 4. §4.2 Multiple process types execute concurrently: initial + always_comb.
//    An initial block sets a value; always_comb reacts to produce output.
// ---------------------------------------------------------------------------
TEST(SimCh4, InitialAndAlwaysCombConcurrent) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  initial a = 8'd10;\n"
      "  always_comb result = a + 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

// ---------------------------------------------------------------------------
// 5. §4.2 Abstraction levels: behavioral (initial block) and dataflow
//    (continuous assignment) coexist and interact.
// ---------------------------------------------------------------------------
TEST(SimCh4, BehavioralAndDataflowCoexist) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  assign b = a + 8'd1;\n"
      "  initial a = 8'd5;\n"
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
  EXPECT_EQ(va->value.ToUint64(), 5u);
  EXPECT_EQ(vb->value.ToUint64(), 6u);
}

// ---------------------------------------------------------------------------
// 6. §4.2 Simulation time: processes scheduled at the same simulation time
//    execute within the same time slot.
// ---------------------------------------------------------------------------
TEST(SimCh4, SameTimeSlotExecution) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 1u);
  EXPECT_EQ(vb->value.ToUint64(), 2u);
}

// ---------------------------------------------------------------------------
// 7. §4.2 Simulation time advances: a delay causes execution at a later
//    simulation time.
// ---------------------------------------------------------------------------
TEST(SimCh4, SimulationTimeAdvances) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    #10 x = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 8. §4.2 Multiple processes across simulation time: two initial blocks
//    with different delays both produce correct final values.
// ---------------------------------------------------------------------------
TEST(SimCh4, MultipleProcessesAcrossTime) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    #5 a = 8'd2;\n"
      "  end\n"
      "  initial begin\n"
      "    b = 8'd10;\n"
      "    #10 b = 8'd20;\n"
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
  EXPECT_EQ(va->value.ToUint64(), 2u);
  EXPECT_EQ(vb->value.ToUint64(), 20u);
}

// ---------------------------------------------------------------------------
// 9. §4.2 Process as concurrently scheduled element: always_comb reacts
//    to changes from an initial block at a later time.
// ---------------------------------------------------------------------------
TEST(SimCh4, AlwaysCombReactsToDelayedChange) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    #5 a = 8'd7;\n"
      "  end\n"
      "  always_comb result = a * 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 14u);
}

// ---------------------------------------------------------------------------
// 10. §4.2 Varying abstraction levels: combinational logic (always_comb)
//     and sequential logic (initial with delays) work together.
// ---------------------------------------------------------------------------
TEST(SimCh4, CombAndSequentialAbstractions) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, sum;\n"
      "  initial begin\n"
      "    a = 8'd3;\n"
      "    b = 8'd4;\n"
      "  end\n"
      "  always_comb sum = a + b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sum");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// ---------------------------------------------------------------------------
// 11. §4.2 Parallel processes: three independent initial blocks all complete.
// ---------------------------------------------------------------------------
TEST(SimCh4, ThreeParallelInitialBlocks) {
  SimCh4Fixture f;
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

// ---------------------------------------------------------------------------
// 13. §4.2 Continuous assignment as a process: assign creates an implicit
//     process that responds to source element changes.
// ---------------------------------------------------------------------------
TEST(SimCh4, ContinuousAssignAsProcess) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] in_val, out_val;\n"
      "  assign out_val = in_val;\n"
      "  initial in_val = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("out_val");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

// ---------------------------------------------------------------------------
// 14. §4.2 Cascade of processes: initial sets a, assign b = a + 1,
//     always_comb c = b * 2. All three execute and propagate.
// ---------------------------------------------------------------------------
TEST(SimCh4, CascadeOfProcesses) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd5;\n"
      "  assign b = a + 8'd1;\n"
      "  always_comb c = b * 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 12u);
}

// ---------------------------------------------------------------------------
// 15. §4.2 Simulation-defined semantics: time slot 0 processes all initial
//     block assignments (simulation is the canonical model).
// ---------------------------------------------------------------------------
TEST(SimCh4, TimeZeroSemantics) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = a + 8'd1;\n"
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
  EXPECT_EQ(va->value.ToUint64(), 1u);
  EXPECT_EQ(vb->value.ToUint64(), 2u);
}

// ---------------------------------------------------------------------------
// 16. §4.2 Concurrent always_comb blocks: two independent always_comb
//     blocks compute results from a shared input.
// ---------------------------------------------------------------------------
TEST(SimCh4, ConcurrentAlwaysCombBlocks) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, r1, r2;\n"
      "  initial a = 8'd10;\n"
      "  always_comb r1 = a + 8'd1;\n"
      "  always_comb r2 = a + 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("r1")->value.ToUint64(), 11u);
  EXPECT_EQ(f.ctx.FindVariable("r2")->value.ToUint64(), 12u);
}

// ---------------------------------------------------------------------------
// 17. §4.2 Process interaction over multiple time steps: initial block
//     updates value at different times, always_comb tracks changes.
// ---------------------------------------------------------------------------
TEST(SimCh4, ProcessInteractionMultipleTimeSteps) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, doubled;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    #5 a = 8'd4;\n"
      "    #5 a = 8'd8;\n"
      "  end\n"
      "  always_comb doubled = a * 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("doubled");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

// ---------------------------------------------------------------------------
// 18. §4.2 Parallel execution with conditional logic: two processes with
//     independent if-else blocks.
// ---------------------------------------------------------------------------
TEST(SimCh4, ParallelConditionalLogic) {
  SimCh4Fixture f;
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
// 19. §4.2 Computation chains in a single process: demonstrates guaranteed
//     sequential computation within a process.
// ---------------------------------------------------------------------------
TEST(SimCh4, ComputationChainInProcess) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    x = 16'd1;\n"
      "    x = x + 16'd1;\n"
      "    x = x * 16'd3;\n"
      "    x = x - 16'd1;\n"
      "  end\n"
      "endmodule\n",
      "x");
  // x = 1, then 2, then 6, then 5.
  EXPECT_EQ(result, 5u);
}

// ---------------------------------------------------------------------------
// 20. §4.2 Multiple continuous assignments as concurrent processes.
// ---------------------------------------------------------------------------
TEST(SimCh4, MultipleContinuousAssignments) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd10;\n"
      "  assign b = a + 8'd1;\n"
      "  assign c = a + 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 11u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 12u);
}

// ---------------------------------------------------------------------------
// 21. §4.2 always_comb with begin-end block: combinational logic with
//     multiple output statements.
// ---------------------------------------------------------------------------
TEST(SimCh4, AlwaysCombWithBeginEnd) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, r1, r2;\n"
      "  initial a = 8'd5;\n"
      "  always_comb begin\n"
      "    r1 = a + 8'd1;\n"
      "    r2 = a + 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // a=5, r1=6, r2=7
  EXPECT_EQ(f.ctx.FindVariable("r1")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("r2")->value.ToUint64(), 7u);
}

// ---------------------------------------------------------------------------
// 22. §4.2 Simulation never goes backwards in time: after two time steps,
//     final values reflect the later assignment.
// ---------------------------------------------------------------------------
TEST(SimCh4, SimulationNeverGoesBackward) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    #10 x = 8'd2;\n"
      "    #10 x = 8'd3;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 3u);
}

// ---------------------------------------------------------------------------
// 23. §4.2 Processes at varying abstraction levels: initial (behavioral),
//     assign (dataflow), and always_comb (combinational) all cooperate.
// ---------------------------------------------------------------------------
TEST(SimCh4, ThreeAbstractionLevels) {
  SimCh4Fixture f;
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

// ---------------------------------------------------------------------------
// 24. §4.2 Empty processes: an initial block with no statements does not
//     interfere with concurrent processes.
// ---------------------------------------------------------------------------
TEST(SimCh4, EmptyProcessNoInterference) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin end\n"
      "  initial a = 8'd77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 77u);
}

// ---------------------------------------------------------------------------
// 25. §4.2 Many parallel processes: stress test with five independent
//     initial blocks.
// ---------------------------------------------------------------------------
TEST(SimCh4, FiveParallelInitialBlocks) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d, e;\n"
      "  initial a = 8'd1;\n"
      "  initial b = 8'd2;\n"
      "  initial c = 8'd3;\n"
      "  initial d = 8'd4;\n"
      "  initial e = 8'd5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("d")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("e")->value.ToUint64(), 5u);
}

// ---------------------------------------------------------------------------
// 26. §4.2 Parallel processes with time delays: interleaved execution across
//     simulation time.
// ---------------------------------------------------------------------------
TEST(SimCh4, InterleavedTimeExecution) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    #5 a = 8'd1;\n"
      "    #10 a = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    #10 b = 8'd2;\n"
      "    #5 b = 8'd4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // a: set 1@t5, set 3@t15. b: set 2@t10, set 4@t15.
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 4u);
}

// ---------------------------------------------------------------------------
// 27. §4.2 Process with loop: sequential execution within an iterative
//     construct inside a single process.
// ---------------------------------------------------------------------------
TEST(SimCh4, ProcessWithLoop) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] sum;\n"
      "  initial begin\n"
      "    integer i;\n"
      "    sum = 0;\n"
      "    for (i = 1; i <= 5; i = i + 1)\n"
      "      sum = sum + i[15:0];\n"
      "  end\n"
      "endmodule\n",
      "sum");
  // 1+2+3+4+5 = 15
  EXPECT_EQ(result, 15u);
}

// ---------------------------------------------------------------------------
// 28. §4.2 Continuous assignment chain: a -> b -> c, all propagate within
//     the same time slot.
// ---------------------------------------------------------------------------
TEST(SimCh4, ContinuousAssignChain) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd7;\n"
      "  assign b = a;\n"
      "  assign c = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 7u);
}

// ---------------------------------------------------------------------------
// 29. §4.2 Processes are concurrently scheduled elements: always_comb
//     re-evaluates when any input changes.
// ---------------------------------------------------------------------------
TEST(SimCh4, AlwaysCombReEvaluatesOnChange) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, a, b, result;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    sel = 8'd0;\n"
      "    #5 sel = 8'd1;\n"
      "  end\n"
      "  always_comb begin\n"
      "    if (sel)\n"
      "      result = b;\n"
      "    else\n"
      "      result = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // After #5, sel=1 so result=b=20.
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// ---------------------------------------------------------------------------
// 30. §4.2 Simulation semantics are canonical: multiple process types
//     (initial, always_comb, assign) all produce deterministic results
//     defined by the simulation model.
// ---------------------------------------------------------------------------
TEST(SimCh4, CanonicalSimulationSemantics) {
  SimCh4Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial a = 8'd4;\n"
      "  assign b = a + 8'd10;\n"
      "  always_comb c = b - 8'd5;\n"
      "  assign d = c * 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // a=4, b=14, c=9, d=18
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 14u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 9u);
  EXPECT_EQ(f.ctx.FindVariable("d")->value.ToUint64(), 18u);
}
