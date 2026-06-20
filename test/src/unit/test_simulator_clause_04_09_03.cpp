#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

TEST(BlockingAssignSchedulingSim, RhsComputedUsingCurrentValuesAtSuspend) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, dst;\n"
      "  initial begin\n"
      "    src = 8'd5;\n"
      "    dst = #10 src;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 src = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("src")->value.ToUint64(), 99u);
}

TEST(BlockingAssignSchedulingSim, RhsMultipleSourcesAllCapturedAtSuspend) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, dst;\n"
      "  initial begin\n"
      "    a = 8'd3;\n"
      "    b = 8'd4;\n"
      "    dst = #10 (a + b);\n"
      "  end\n"
      "  initial begin\n"
      "    #2 a = 8'd99;\n"
      "    #5 b = 8'd11;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 99u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 11u);
}

TEST(BlockingAssignSchedulingSim, ProcessSuspendsAndScheduledAsFutureEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    b = #10 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 99u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

TEST(BlockingAssignSchedulingSim, ZeroDelayFromActiveContextRoutesToInactive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] b, snap, done;\n"
      "  initial begin\n"
      "    b = 8'd0;\n"
      "    snap = 8'd0;\n"
      "    b <= 8'd7;\n"
      "    done = #0 8'd1;\n"
      "    snap = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("done")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 7u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(BlockingAssignSchedulingSim,
     ZeroDelayFromReactiveContextRoutesToReInactive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] b, snap, done;\n"
      "  program p;\n"
      "    initial begin\n"
      "      b = 8'd0;\n"
      "      snap = 8'd0;\n"
      "      b <= 8'd7;\n"
      "      done = #0 8'd1;\n"
      "      snap = b;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("done")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 7u);
}

TEST(BlockingAssignSchedulingSim, ResumeEnablesEventsOnLhsUpdate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sig, trig;\n"
      "  initial begin\n"
      "    sig = 8'd0;\n"
      "    trig = 8'd0;\n"
      "    sig = #5 8'd1;\n"
      "  end\n"
      "  always @(sig) trig = 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("sig")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("trig")->value.ToUint64(), 1u);
}

TEST(BlockingAssignSchedulingSim, TargetEvaluatedAtResumeTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:1];\n"
      "  int idx;\n"
      "  initial begin\n"
      "    mem[0] = 8'd0;\n"
      "    mem[1] = 8'd0;\n"
      "    idx = 0;\n"
      "    mem[idx] = #10 8'hCC;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 idx = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("mem[0]")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("mem[1]")->value.ToUint64(), 0xCCu);
}

TEST(BlockingAssignSchedulingSim, ContinuesWithNextStatementAndOtherEvents) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] b, c, parallel_marker;\n"
      "  initial begin\n"
      "    b = 8'd0;\n"
      "    c = 8'd0;\n"
      "    parallel_marker = 8'd0;\n"
      "    b = #10 8'd1;\n"
      "    c = 8'd2;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 parallel_marker = 8'd9;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("parallel_marker")->value.ToUint64(), 9u);
}

// §4.9.3 also covers the case where the assigning process returns immediately
// because no intra-assignment delay is specified: it still performs the update
// of the left-hand side and enables any events that depend on that update. This
// exercises the immediate (no-delay) execution path, which is dispatched
// separately from the delayed path, so the event-enabling behavior is verified
// on its own rather than being inferred from the delayed cases above.
TEST(BlockingAssignSchedulingSim,
     ImmediateAssignNoDelayEnablesEventsOnLhsUpdate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sig, trig;\n"
      "  initial begin\n"
      "    sig = 8'd0;\n"
      "    trig = 8'd0;\n"
      "    sig = 8'd1;\n"
      "  end\n"
      "  always @(sig) trig = 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("sig")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("trig")->value.ToUint64(), 1u);
}
