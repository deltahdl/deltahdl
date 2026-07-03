
#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NonblockingAssignSim, OrderingPreservedAcrossInitials) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'd99;\n"
      "    #8 a <= #8 8'd1;\n"
      "  end\n"
      "  initial begin\n"
      "    #12 a <= #4 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0u);
}

TEST(NonblockingAssignSim, BlockingEventsFromNbaProcessedAfter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic q;\n"
      "  logic post_q;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    q = 0;\n"
      "    post_q = 0;\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "  always_ff @(posedge clk) q <= 1;\n"
      "  always @(q) post_q = q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("q")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("post_q")->value.ToUint64(), 1u);
}

TEST(NonblockingAssignSim, ProceduralFlowNotBlockedBySubsequent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] tgt;\n"
      "  logic [7:0] sample;\n"
      "  initial begin\n"
      "    tgt = 8'd5;\n"
      "    tgt <= 8'd99;\n"
      "    sample = tgt;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("sample")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("tgt")->value.ToUint64(), 99u);
}

TEST(NonblockingAssignSim, LhsRequiringEvaluationBindsAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:1];\n"
      "  int idx;\n"
      "  initial begin\n"
      "    arr[0] = 8'd0;\n"
      "    arr[1] = 8'd0;\n"
      "    idx = 0;\n"
      "    arr[idx] <= 8'hAA;\n"
      "    idx = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xAAu);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0u);
}

// §10.4.2 Example 3 / two-step rule: a nonblocking assignment evaluates in two
// steps -- every right-hand side in the time step is sampled before any
// left-hand side is updated. Two NBAs that read each other's variables
// therefore exchange values: each RHS observes the pre-update value. A naive
// sequential (blocking-style) execution would instead leave both variables
// holding b's original value, so a genuine swap rules that misreading out.
TEST(NonblockingAssignSim, SwapExchangesValuesInTwoSteps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    a <= b;\n"
      "    b <= a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 10u);
}

// §10.4.2 Example 7: intra-assignment-delayed nonblocking assignments in a loop
// make assignments to the same variable "without cancelling previous
// assignments". The loop runs entirely at time 0, scheduling six updates of
// i[0] = 0,1,0,1,0,1 at times 0,10,20,30,40,50. Each scheduled update must
// carry its own sampled value and fire at its own time -- a single shared
// pending slot would let the last-scheduled value win everywhere and drop the
// intervening updates. A second block strobes r1 mid-window to observe the
// distinct values as they take effect.
TEST(NonblockingAssignSim, DelayedNbasToSameVarDoNotCancelEachOther) {
  SimFixture f;
  auto* design = ElaborateLowerRun(f,
                                   "module t;\n"
                                   "  logic r1;\n"
                                   "  logic [2:0] i;\n"
                                   "  logic s0, s1, s2, s3;\n"
                                   "  initial begin\n"
                                   "    for (i = 0; i <= 5; i = i + 1)\n"
                                   "      r1 <= #(i * 10) i[0];\n"
                                   "  end\n"
                                   "  initial begin\n"
                                   "    #5  s0 = r1;\n"
                                   "    #10 s1 = r1;\n"
                                   "    #10 s2 = r1;\n"
                                   "    #10 s3 = r1;\n"
                                   "  end\n"
                                   "endmodule\n");
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(f.ctx.FindVariable("s0")->value.ToUint64(), 0u);  // t=5,  update@0
  EXPECT_EQ(f.ctx.FindVariable("s1")->value.ToUint64(), 1u);  // t=15, update@10
  EXPECT_EQ(f.ctx.FindVariable("s2")->value.ToUint64(), 0u);  // t=25, update@20
  EXPECT_EQ(f.ctx.FindVariable("s3")->value.ToUint64(), 1u);  // t=35, update@30
}

}  // namespace
