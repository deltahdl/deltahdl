#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(InitialProcedureSimulation, InitialBlockSchedulesEvent) {
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

TEST(InitialProcedureSimulation, InitialBlockExecutes) {
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

TEST(InitialProcedureSimulation, NoSensitivityRegistered) {
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

  const auto& procs = f.ctx.GetSensitiveProcesses("x");
  EXPECT_TRUE(procs.empty());
}

TEST(InitialProcedureSimulation, EmptyInitialDoesNotInterfere) {
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

TEST(InitialProcedureSimulation, SequentialBlockingAssignmentsAtTimeZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = a + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}});
}

TEST(InitialProcedureSimulation, InitialCeasesWhenStatementFinishes) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x = 1;\n"
      "    x = x + 1;\n"
      "    x = x + 1;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 3u);
}

TEST(InitialProcedureSimulation, ExecutesExactlyOnce) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    count = count + 1;\n"
      "  end\n"
      "endmodule\n",
      "count");
  EXPECT_EQ(val, 1u);
}

TEST(InitialProcedureSimulation, InitialWithDelayCeases) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    #5 x = 42;\n"
      "  end\n"
      "  initial #10 $finish;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

TEST(InitialProcedureSimulation, DoesNotRerunWhenReferencedSignalChanges) {
  // An initial procedure runs a single time and stays finished afterward. Even
  // when a variable it read is driven again later in the run, the completed
  // procedure must not be resumed. If it were wrongly resensitized like an
  // always block, the running total below would advance past its time-zero
  // value once trig changes at time 5.
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] runs;\n"
      "  logic [7:0] trig;\n"
      "  initial begin\n"
      "    runs = 0;\n"
      "    trig = 8'd0;\n"
      "    runs = runs + trig + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 trig = 8'd9;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      "runs");
  EXPECT_EQ(val, 1u);
}

TEST(InitialProcedureSimulation, IteratingBodyRunsOnceThenCeases) {
  // §9.2.1 example 1 form: an initial whose body performs iterative
  // initialization (a for-loop over a memory-like accumulation). The whole
  // procedure — loop included — executes a single time and then its activity
  // ceases. The second initial perturbs `step` after the first has finished; if
  // the finished procedure were wrongly restarted, `total` would be recomputed
  // with step==100 (or keep accumulating) instead of staying at the single-pass
  // total of 4 (four iterations of +1).
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] total;\n"
      "  logic [7:0] step;\n"
      "  initial begin\n"
      "    total = 0;\n"
      "    step = 8'd1;\n"
      "    for (int i = 0; i < 4; i++)\n"
      "      total = total + step;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 step = 8'd100;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      "total");
  EXPECT_EQ(val, 4u);
}

TEST(InitialProcedureSimulation, WaveformStimulusCeasesAtLastPattern) {
  // §9.2.1 example 2 form: an initial used to drive a stimulus waveform as a
  // sequence of delayed assignments. The procedure marches through each pattern
  // exactly once and its activity ceases once the last pattern has been driven;
  // it does not loop back like an always procedure. Sampling well after the
  // final delay (finish at time 100, last pattern applied at time 40) must show
  // the last pattern still held.
  auto val = RunAndGet(
      "module m;\n"
      "  logic [5:0] inputs;\n"
      "  initial begin\n"
      "    inputs = 6'b000000;\n"
      "    #10 inputs = 6'b011001;\n"
      "    #10 inputs = 6'b011011;\n"
      "    #10 inputs = 6'b011000;\n"
      "    #10 inputs = 6'b001000;\n"
      "  end\n"
      "  initial #100 $finish;\n"
      "endmodule\n",
      "inputs");
  EXPECT_EQ(val, 0b001000u);
}

TEST(InitialProcedureSimulation, NullStatementInitialCompletes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial ;\n"
      "  initial x = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 55u);
}

}  // namespace
