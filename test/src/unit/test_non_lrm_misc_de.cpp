// Non-LRM tests

#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(VpiAnnexK2, VpiTimeDefaultInit) {
  s_vpi_time time = {};
  EXPECT_EQ(time.type, 0);
  EXPECT_EQ(time.high, 0u);
  EXPECT_EQ(time.low, 0u);
  EXPECT_DOUBLE_EQ(time.real, 0.0);
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
// 29. §4.2 Processes are concurrently scheduled elements: always_comb
//     re-evaluates when any input changes.
// ---------------------------------------------------------------------------
TEST(SimCh4, AlwaysCombReEvaluatesOnChange) {
  SimFixture f;
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

}  // namespace
