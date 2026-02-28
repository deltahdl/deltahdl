// §9.2.2.2: Combinational logic always_comb procedure

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(Lowerer, AlwaysCombRetrigger) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  always_comb b = a + 1;\n"
      "  initial begin\n"
      "    a = 5;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 6u);
}

TEST(Lowerer, AlwaysCombAutoTriggerTimeZero) {
  // IEEE §9.2: always_comb auto-triggers once at time zero.
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] b;\n"
      "  always_comb b = 42;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 42u);
}

TEST(Lowerer, SensitivityMapPopulated) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  always_comb b = a + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  // Sensitivity map should have signal 'a' mapped to a process.
  const auto& procs = f.ctx.GetSensitiveProcesses("a");
  EXPECT_FALSE(procs.empty());
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
// 4. §4.2 Multiple process types execute concurrently: initial + always_comb.
//    An initial block sets a value; always_comb reacts to produce output.
// ---------------------------------------------------------------------------
TEST(SimCh4, InitialAndAlwaysCombConcurrent) {
  SimFixture f;
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
// 10. §4.2 Varying abstraction levels: combinational logic (always_comb)
//     and sequential logic (initial with delays) work together.
// ---------------------------------------------------------------------------
TEST(SimCh4, CombAndSequentialAbstractions) {
  SimFixture f;
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
// 16. §4.2 Concurrent always_comb blocks: two independent always_comb
//     blocks compute results from a shared input.
// ---------------------------------------------------------------------------
TEST(SimCh4, ConcurrentAlwaysCombBlocks) {
  SimFixture f;
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
// 21. §4.2 always_comb with begin-end block: combinational logic with
//     multiple output statements.
// ---------------------------------------------------------------------------
TEST(SimCh4, AlwaysCombWithBeginEnd) {
  SimFixture f;
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

}  // namespace
