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

TEST(GeneralPurposeAlwaysSimulation, AlwaysRepeatsContinuously) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] count;\n"
      "  initial count = 0;\n"
      "  always #1 count = count + 1;\n"
      "  initial #10 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
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
