// §12.7.1: The for-loop

#include "simulator/lowerer.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// --- for ---
// §12.7.1: for loop — basic accumulation
TEST(SimA608, ForBasic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    for (int i = 0; i < 5; i = i + 1)\n"
      "      total = total + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// §12.7.1: for with typed init — variable used in body
TEST(SimA608, ForTypedInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sum;\n"
      "  initial begin\n"
      "    sum = 8'd0;\n"
      "    for (int i = 1; i <= 4; i = i + 1)\n"
      "      sum = sum + i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sum");
  ASSERT_NE(var, nullptr);
  // 1 + 2 + 3 + 4 = 10
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// §12.7.1: for with empty init/cond/step — for(;;) with break
TEST(SimA608, ForAllEmptyWithBreak) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    for (;;) begin\n"
      "      if (x == 8'd4) break;\n"
      "      x = x + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

// §12.7.1: for_step with inc_or_dec_expression (i++)
TEST(SimA608, ForStepIncrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    for (int i = 0; i < 3; i++)\n"
      "      x = x + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
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

}  // namespace
