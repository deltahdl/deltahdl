#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(GeneralPurposeAlwaysSimulation, ClockOscillatorWithDelay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] clk;\n"
      "  initial clk = 0;\n"
      "  always #5 clk = clk + 1;\n"
      "  initial #25 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("clk");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// §9.2.2.1's second example uses a parameter as the delay value
// (`always #half_period areg = ~areg;`), unlike the literal-delay form above.
// A parameter is a §11.2.1 constant expression and, per §9.4, is lowered to a
// live delay rather than folded to a literal. This drives the general-purpose
// always through the full pipeline with a parameter timing control and observes
// that it repeats: the counter advances once per delay period, so a nonzero end
// value can only arise from the block executing more than once.
TEST(GeneralPurposeAlwaysSimulation, RepeatsUnderParameterDelay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter half_period = 5;\n"
      "  logic [31:0] areg;\n"
      "  initial areg = 0;\n"
      "  always #half_period areg = areg + 1;\n"
      "  initial #22 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("areg");
  ASSERT_NE(var, nullptr);
  // Fires at t=5,10,15,20 before the #22 finish: four repetitions.
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

// A localparam is the third §11.2.1 constant form admitted as the delay value
// (alongside a literal and a parameter). Per §9.4, it is lowered to a live
// delay via its own is_localparam path rather than folded to a literal, so it
// takes a distinct code path from the parameter form above. Same observation:
// the general-purpose always loops under a localparam-valued timing control.
TEST(GeneralPurposeAlwaysSimulation, RepeatsUnderLocalparamDelay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam step = 5;\n"
      "  logic [31:0] areg;\n"
      "  initial areg = 0;\n"
      "  always #step areg = areg + 1;\n"
      "  initial #22 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("areg");
  ASSERT_NE(var, nullptr);
  // Fires at t=5,10,15,20 before the #22 finish: four repetitions.
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(GeneralPurposeAlwaysSimulation, TwoPhaseClockBeginEnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  initial clk = 0;\n"
      "  always begin\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "  end\n"
      "  initial #20 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("clk");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(GeneralPurposeAlwaysSimulation, SensitivityListTriggersOnEdge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    d = 1;\n"
      "    q = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 1u);
}

}  // namespace
