#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

// §9.2.2: there are four forms of always procedures -- always, always_comb,
// always_latch, and always_ff -- and every one of them repeats continuously for
// the whole duration of the simulation (in contrast to a one-shot initial).
// Each test below builds one form from real source, runs it through the full
// pipeline, and observes the body executing more than once.

namespace {

// Form 1: the general-purpose `always` with delay timing control keeps looping,
// so a counter it drives advances well past a single execution before $finish.
TEST(AlwaysRepeatsSim, GeneralPurposeAlwaysWithDelayLoops) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer count;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    #55 $finish;\n"
      "  end\n"
      "  always #10 count = count + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* count = f.ctx.FindVariable("count");
  ASSERT_NE(count, nullptr);
  // Increments at t=10,20,30,40,50 before the #55 finish -> five iterations.
  EXPECT_EQ(count->value.ToUint64(), 5u);
}

// Form 1 again, but the event-controlled `always @(posedge)` variant: it also
// re-arms after each firing, so repeated clock edges each run the body once
// more.
TEST(AlwaysRepeatsSim, GeneralPurposeAlwaysWithEventControlLoops) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  reg clk;\n"
      "  integer n;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    n = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  always @(posedge clk) n = n + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* n = f.ctx.FindVariable("n");
  ASSERT_NE(n, nullptr);
  // Two posedges (t=5, t=15) each re-run the body -> n reaches 2.
  EXPECT_EQ(n->value.ToUint64(), 2u);
}

// Form 2: always_comb re-evaluates on every input change, not just once at time
// zero. Two successive changes each re-run it, so the final result reflects the
// last input rather than the first.
TEST(AlwaysRepeatsSim, AlwaysCombReevaluatesOnEachChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, y;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    #5 a = 8'd5;\n"
      "    #5 a = 8'd9;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  always_comb y = a + 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // Only continuous re-evaluation makes y track the final a=9 -> y=10.
  EXPECT_EQ(y->value.ToUint64(), 10u);
}

// Form 3: always_latch likewise re-runs on every change of a signal it reads,
// so while the enable is held high a second data change is captured by a second
// evaluation.
TEST(AlwaysRepeatsSim, AlwaysLatchReevaluatesWhileEnabled) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d, q;\n"
      "  initial begin\n"
      "    en = 1'b0;\n"
      "    d = 8'd0;\n"
      "    #5 en = 1'b1;\n"
      "    d = 8'd3;\n"
      "    #5 d = 8'd7;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  always_latch if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  // First evaluation with en=1 latches 3; the later d=7 change re-runs the
  // block and latches 7 -> proves the block repeated.
  EXPECT_EQ(q->value.ToUint64(), 7u);
}

// Form 4: always_ff re-arms on its edge event control, running the body once
// per clock edge for the whole simulation.
TEST(AlwaysRepeatsSim, AlwaysFfFiresOnEachClockEdge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  reg clk;\n"
      "  integer count;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    count = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  always_ff @(posedge clk) count <= count + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* count = f.ctx.FindVariable("count");
  ASSERT_NE(count, nullptr);
  // Three posedges (t=5, t=15, t=25) each fire the flop -> count reaches 3.
  EXPECT_EQ(count->value.ToUint64(), 3u);
}

}  // namespace
