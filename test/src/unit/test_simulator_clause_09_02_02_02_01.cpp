// §9.2.2.2.1: Implicit always_comb sensitivities

#include "simulation/lowerer.h"
#include "simulation/variable.h"

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
// 9. §4.2 Process as concurrently scheduled element: always_comb reacts
//    to changes from an initial block at a later time.
// ---------------------------------------------------------------------------
TEST(SimCh4, AlwaysCombReactsToDelayedChange) {
  SimFixture f;
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

}  // namespace
