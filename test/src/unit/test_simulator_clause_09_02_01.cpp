// §9.2.1: Initial procedures


#include "simulation/lowerer.h"
#include "simulation/net.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(Lowerer, InitialBlockSchedulesEvent) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_TRUE(f.scheduler.HasEvents());
}

TEST(Lowerer, InitialBlockExecutes) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(Lowerer, SensitivityMapEmpty) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  // Initial blocks don't contribute to sensitivity map.
  const auto& procs = f.ctx.GetSensitiveProcesses("x");
  EXPECT_TRUE(procs.empty());
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
static uint64_t RunAndGet(const std::string& src, const char* var_name) {
  SimFixture f;
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
  SimFixture f;
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
// 24. §4.2 Empty processes: an initial block with no statements does not
//     interfere with concurrent processes.
// ---------------------------------------------------------------------------
TEST(SimCh4, EmptyProcessNoInterference) {
  SimFixture f;
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
  SimFixture f;
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

}  // namespace
