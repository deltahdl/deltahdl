
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
  ExpectNonblockingPairExchangesValues(f);
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

// §10.4.2 gives the nonblocking form the same target the blocking form takes:
// "In this syntax, variable_lvalue is a data type that is valid for a
// procedural assignment statement", and §11.4.12 makes a concatenation one of
// those -- "The concatenation is treated as a packed vector of bits. It can be
// used on the left-hand side of an assignment". So `{a, b} <= 16'h1234` has to
// distribute across a and b exactly as `{a, b} = 16'h1234` does, a taking the
// high byte and b the low one. It did not: ScheduleNonblockingAssign carried an
// arm for a streaming concatenation and none for a plain one, and
// ResolveLhsVariable answers null for a concatenation, so the statement fell
// out of the bottom of the function having scheduled no write and reported no
// diagnostic. This is the IsConcatLhs gate and the ScheduleConcatNba arm behind
// it. Both variables are pre-loaded with sentinels that neither expected value
// can be, because a target left holding its old value is what the defect
// produced; starting them at zero would let "scheduled nothing at all" pass as
// "assigned zero".
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

// §10.4.2: a nonblocking assignment "evaluates the right-hand side expression,
// schedules the assignment ... to occur at the end of the current time step",
// so the statement after it still reads what the target held before. A
// concatenation target is under the same rule, since the clause distinguishes
// its left-hand sides only by what a procedural assignment accepts. Reading a
// into sample on the very next statement therefore has to answer the old byte
// while a ends the time step holding the new one. This is what the deferral in
// ScheduleConcatNba claims: the unpacker runs from inside an update-region
// callback, not where the statement executed. Doing the distribution eagerly at
// schedule time would leave sample holding 0x12.
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

// §10.9 gives a positional assignment pattern the same standing on the left of
// an assignment that §11.4.12 gives a concatenation, and §10.4.2 asks only that
// the target be one a procedural assignment accepts, so `'{a, b} <= 16'h5678`
// distributes where `'{a, b} = 16'h5678` does. The bare-pattern spelling
// reaches the new arm through IsConcatLhs's kAssignmentPattern case rather than
// its kConcatenation one, and before the fix it too scheduled nothing and
// reported nothing. The elaboration is required to be clean as well as
// non-null: §10.9 rules on a left-hand pattern's notation and bit count, and a
// case that only read the values back could not tell a source the elaborator
// accepted from one it rejected. Sentinels again, for the reason
// ConcatenationTargetDistributesToItsElements gives.
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

// §11.4.1 gives a select element of a concatenation target the bits its own
// indices name and no others, so `{a[3:0], b} <= 12'h9AB` writes the low nibble
// of a and leaves the high nibble standing: a ends at 0xF9, not 0x09. This is
// the case that pins the design of the new arm rather than merely its
// existence. Resolving the elements where the statement executes and scheduling
// a whole-variable write for each would answer 0x09, because ResolveLhsVariable
// on a select hands back the whole of the variable selected from -- the
// boundary error ConcatLhsElemWidth records having already been made once on
// the blocking side. Deferring the blocking unpacker instead keeps
// WriteBitSelect as the writer, so the window is the one the element named.
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

}  // namespace
