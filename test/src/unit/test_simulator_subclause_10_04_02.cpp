#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_nonblocking_swap.h"
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
      "  logic q = 0;\n"
      "  logic post_q;\n"
      "  initial begin\n"
      "    clk = 0;\n"
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

TEST(NonblockingAssignSim, SwapExchangesValuesInTwoSteps) {
  SimFixture f;
  ExpectNonblockingPairExchangesValues(f);
}

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
  EXPECT_EQ(f.ctx.FindVariable("s0")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("s1")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("s2")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("s3")->value.ToUint64(), 1u);
}

TEST(NonblockingAssignSim, ConcatenationTargetDistributesToItsElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    b = 8'h5A;\n"
      "    {a, b} <= 16'h1234;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0x12u}, {"b", 0x34u}});
}

TEST(NonblockingAssignSim, ConcatenationTargetIsWrittenInTheNbaRegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [7:0] sample;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    b = 8'd6;\n"
      "    {a, b} <= 16'h1234;\n"
      "    sample = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"sample", 5u}, {"a", 0x12u}, {"b", 0x34u}});
}

TEST(NonblockingAssignSim, AssignmentPatternTargetDistributesToItsElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hC3;\n"
      "    b = 8'h3C;\n"
      "    '{a, b} <= 16'h5678;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerRunAndCheck(f, design, {{"a", 0x56u}, {"b", 0x78u}});
}

TEST(NonblockingAssignSim,
     TypedAssignmentPatternTargetDistributesToItsElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'h11;\n"
      "    b = 8'h22;\n"
      "    pair_t'{a, b} <= 16'hBEEF;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerRunAndCheck(f, design, {{"a", 0xBEu}, {"b", 0xEFu}});
}

TEST(NonblockingAssignSim, ConcatenationTargetWritesOnlyTheBitsASelectNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'hFF;\n"
      "    {a[3:0], b} <= 12'h9AB;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0xF9u}, {"b", 0xABu}});
}

TEST(NonblockingAssignSim,
     ConcatenationTargetSelectElementWakesAnEventControlOnItsVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int wakes;\n"
      "  initial begin\n"
      "    wakes = 0;\n"
      "    #1 a = 8'h50;\n"
      "    b = 8'h0F;\n"
      "    #1 {a[3:0], b} <= 12'h6C7;\n"
      "  end\n"
      "  always @(a) wakes = wakes + 1;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"wakes", 2u}, {"a", 0x56u}, {"b", 0xC7u}});
}

TEST(NonblockingAssignSim,
     SelectTargetWithANegativeBoundWritesInRangeBitsOnly) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    b = 8'h00;\n"
      "    a[1:-2] <= 4'b1101;\n"
      "    b[1:-2] = 4'b1101;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0x03u}, {"b", 0x03u}});
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), b->value.ToUint64());
}

TEST(NonblockingAssignSim, SelectTargetRunningOffLowEndWritesItsOwnHighBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    a[1 -: 4] <= 4'b1101;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0x03u}});
}

TEST(NonblockingAssignSim,
     SelectTargetResolvesItsIndicesAgainstTheDeclaredRange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:8] a;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    a[9:8] <= 2'b11;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0x03u}});
}

TEST(NonblockingAssignSim, SelectTargetRunningOffHighEndStillTakesItsLowBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    a[9:6] <= 4'b1101;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0x40u}});
}

TEST(NonblockingAssignSim, MultidimElementTargetWritesTheElement) {
  SimFixture f;
  auto* elem = RunAndFindVar(
      "module t;\n"
      "  int A[2][3];\n"
      "  initial begin\n"
      "    A[1][2] <= 43;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "A[1][2]");
  ASSERT_NE(elem, nullptr);
  EXPECT_EQ(elem->value.ToUint64(), 43u);
}

TEST(NonblockingAssignSim, MultidimElementTargetLeavesTheArrayBaseAlone) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[2][3];\n"
      "  initial begin\n"
      "    A[1][2] <= 43;\n"
      "    A[0][1] <= 5;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"A", 0u}, {"A[1][2]", 43u}, {"A[0][1]", 5u}});
}

TEST(NonblockingAssignSim, ClassPropertyTargetReceivesTheScheduledWrite) {
  SimFixture f;
  auto* sampled = RunAndFindVar(
      "class C;\n"
      "  logic [7:0] f;\n"
      "endclass\n"
      "module t;\n"
      "  C h;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.f = 8'h11;\n"
      "    h.f <= 8'hA5;\n"
      "    #1 r = h.f;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(sampled, nullptr);
  EXPECT_EQ(sampled->value.ToUint64(), 0xA5u);
}

TEST(NonblockingAssignSim, ClassHandleInTheTargetIsResolvedAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  logic [7:0] f;\n"
      "endclass\n"
      "module t;\n"
      "  C h;\n"
      "  C other;\n"
      "  C keep;\n"
      "  logic [7:0] r;\n"
      "  logic [7:0] seen;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    other = new;\n"
      "    keep = h;\n"
      "    h.f = 8'h11;\n"
      "    other.f = 8'h22;\n"
      "    h.f <= 8'hA5;\n"
      "    h = other;\n"
      "    #1 r = keep.f;\n"
      "    seen = other.f;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerRunAndCheck(f, design, {{"r", 0xA5u}, {"seen", 0x22u}});
}

TEST(NonblockingAssignSim, PropertyNamedBareOrThroughThisInAMethod) {
  auto val = RunAndGet(
      "module t;\n"
      "  int mv;\n"
      "  int result;\n"
      "  class C;\n"
      "    int x, y;\n"
      "    function void f();\n"
      "      x <= 71;\n"
      "      this.y <= 72;\n"
      "      mv <= 73;\n"
      "    endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.f();\n"
      "    #1 result = h.x * 10000 + h.y * 100 + mv;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 717273u);
}

TEST(NonblockingAssignSim, PropertyNamedInAClassTaskWithAndWithoutADelay) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  class C;\n"
      "    int z, w;\n"
      "    int seen;\n"
      "    task run();\n"
      "      this.z <= 5;\n"
      "      w <= #2 9;\n"
      "      #1 seen = z * 10 + w;\n"
      "      #1 seen = seen * 10 + w;\n"
      "    endtask\n"
      "  endclass\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.run();\n"
      "    #1 result = h.seen * 100 + h.z * 10 + h.w;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 50059u);
}

TEST(NonblockingAssignSim, BitSelectIndexEvaluatedOnce) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  int i;\n"
      "  initial begin\n"
      "    v = 8'h00;\n"
      "    v[i++] <= 1'b1;\n"
      "    #1 $display(\"%0d %b\", i, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 00000001\n");
}

TEST(NonblockingAssignSim, AnEventControlledUpdateKeepsTheIndexOfItsExecution) {
  const char* src =
      "module t;\n"
      "  logic [7:0] arr[0:1];\n"
      "  int idx;\n"
      "  event e;\n"
      "  logic [7:0] a0, a1;\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; idx = 0;\n"
      "    arr[idx] <= @(e) 8'hAA;\n"
      "    idx = 1;\n"
      "    #1 ->e;\n"
      "    #1 a0 = arr[0]; a1 = arr[1];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a0"), 0xAAu);
  EXPECT_EQ(RunAndGet(src, "a1"), 0u);
}

TEST(NonblockingAssignSim,
     AConcatenationElementsHandleAndIndexAreTheExecutions) {
  const char* src =
      "class C; logic [7:0] f; endclass\n"
      "module t;\n"
      "  typedef struct { logic [7:0] f; } s_t;\n"
      "  C h, first, other;\n"
      "  s_t arr[2];\n"
      "  int i;\n"
      "  logic [7:0] b, c;\n"
      "  logic [7:0] first_f, other_f, a0, a1;\n"
      "  initial begin\n"
      "    first = new; other = new; h = first;\n"
      "    first.f = 0; other.f = 0; arr[0].f = 0; arr[1].f = 0; i = 0;\n"
      "    {h.f, b} <= 16'hAA55;\n"
      "    {arr[i].f, c} <= 16'hBB66;\n"
      "    h = other; i = 1;\n"
      "    #1 first_f = first.f; other_f = other.f; a0 = arr[0].f; a1 = "
      "arr[1].f;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "first_f"), 0xAAu);
  EXPECT_EQ(RunAndGet(src, "other_f"), 0u);
  EXPECT_EQ(RunAndGet(src, "a0"), 0xBBu);
  EXPECT_EQ(RunAndGet(src, "a1"), 0u);
}

TEST(NonblockingAssignSim,
     IntraAssignmentDelayWritesTheInstanceTheVirtualInterfaceHeldAtExecution) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface I; logic s = 0; endinterface\n"
                       "module t;\n"
                       "  I i1(), i2();\n"
                       "  virtual I v;\n"
                       "  initial begin\n"
                       "    v = i1;\n"
                       "    v.s <= #5 1;\n"
                       "    #2 v = i2;\n"
                       "    #5 $display(\"%b %b\", i1.s, i2.s);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(NonblockingAssignSim, IntraAssignmentDelaysOfBlockingAndNonblockingForms) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic a, b, c, d, e, g;\n"
                       "  initial begin a = #10 1; b = #2 0; c = #4 1; end\n"
                       "  initial begin d <= #10 1; e <= #2 0; g <= #4 1; end\n"
                       "  initial begin\n"
                       "    #3 $display(\"%b%b%b %b%b%b\", a, b, c, d, e, g);\n"
                       "    #2 $display(\"%b%b%b %b%b%b\", a, b, c, d, e, g);\n"
                       "    #6 $display(\"%b%b%b %b%b%b\", a, b, c, d, e, g);\n"
                       "    #2 $display(\"%b%b%b %b%b%b\", a, b, c, d, e, g);\n"
                       "    #4 $display(\"%b%b%b %b%b%b\", a, b, c, d, e, g);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "xxx x0x\nxxx x01\n1xx 101\n10x 101\n101 101\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(NonblockingAssignSim, EqualDelayUpdatesOfOneBlockLandInExecutionOrder) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic a;\n"
                       "  initial a = 1;\n"
                       "  initial begin a <= #4 0; a <= #4 1; end\n"
                       "  initial #5 $display(\"%b\", a);\n"
                       "endmodule\n",
                       f),
            "1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
