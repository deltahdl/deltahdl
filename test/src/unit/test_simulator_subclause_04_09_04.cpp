#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

using namespace delta;

TEST(NonblockingAssignSchedulingSim, SchedulesUpdateInNbaRegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst, snap;\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    snap = 8'd0;\n"
      "    dst <= 8'd7;\n"
      "    snap = dst;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 7u);
}

TEST(NonblockingAssignSchedulingSim, ZeroDelaySchedulesInCurrentTimestep) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    dst <= 8'd5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 5u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(NonblockingAssignSchedulingSim, NonzeroDelaySchedulesAsFutureEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst, mid;\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    mid = 8'd0;\n"
      "    dst <= #10 8'd99;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 mid = dst;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("mid")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 99u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

TEST(NonblockingAssignSchedulingSim, RhsUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, dst;\n"
      "  initial begin\n"
      "    src = 8'd5;\n"
      "    dst = 8'd0;\n"
      "    dst <= src;\n"
      "    src = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("src")->value.ToUint64(), 99u);
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 5u);
}

TEST(NonblockingAssignSchedulingSim, LhsTargetUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:1];\n"
      "  int idx;\n"
      "  initial begin\n"
      "    mem[0] = 8'd0;\n"
      "    mem[1] = 8'd0;\n"
      "    idx = 0;\n"
      "    mem[idx] <= 8'hCC;\n"
      "    idx = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("mem[0]")->value.ToUint64(), 0xCCu);
  EXPECT_EQ(f.ctx.FindVariable("mem[1]")->value.ToUint64(), 0u);
}

// §4.9.4 claim 3, left-hand-target half over a bit-select lvalue (distinct
// scheduling path from the unpacked-array-element form above): the target bit
// index is sampled when the update is placed. Changing the index variable
// afterward must not redirect the deferred write. Built from real `<=` bit-
// select syntax and run end-to-end.
TEST(NonblockingAssignSchedulingSim,
     LhsBitSelectTargetUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  int idx;\n"
      "  initial begin\n"
      "    dst = 8'h00;\n"
      "    idx = 0;\n"
      "    dst[idx] <= 1'b1;\n"
      "    idx = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // Bit 0 (the index in effect at scheduling), not bit 3, is written.
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 0x01u);
}

// §4.9.4 claim 3, right-hand-value half for two nonblocking assignments placed
// in the same NBA region: both right-hand sides read the values in effect when
// the updates are placed, so neither observes the other's update. The classic
// swap must exchange the two variables. Exercises the §10.4.2 `<=` statement
// and §4.4.2.4 NBA region from real source, driven through the full pipeline.
TEST(NonblockingAssignSchedulingSim, ConcurrentNbaWritesUsePreUpdateValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = 8'd2;\n"
      "    a <= b;\n"
      "    b <= a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 1u);
}

// §4.9.4 claim 1, in the edge-triggered procedural position: a nonblocking
// assignment inside a clocked always block schedules an NBA update rather than
// taking effect immediately. A blocking read of the target later in the same
// process observes the pre-update value, and the NBA update lands afterward in
// the NBA region. Built from real §10.4.2 `<=` plus event-control syntax.
TEST(NonblockingAssignSchedulingSim,
     ClockedNonblockingUpdateDeferredToNbaRegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] d, q, snap;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    d = 8'hAB;\n"
      "    q = 8'h00;\n"
      "    snap = 8'h00;\n"
      "    #5 clk = 1'b1;\n"
      "  end\n"
      "  always @(posedge clk) begin\n"
      "    q <= d;\n"
      "    snap = q;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // snap captured q before the deferred update; q holds the NBA result.
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 0x00u);
  EXPECT_EQ(f.ctx.FindVariable("q")->value.ToUint64(), 0xABu);
}

// Runs `src` and checks that the select assignment in it wrote no bit of `x`
// and cost the scheduler no event.
//
// The free count alone cannot say the second thing. EventPool hands out events
// the Arena makes on demand, so a count read at the end of a run reports
// whatever the arena happened to build and not how much of it came back; the
// stock is primed to a known size first, and what the check then reads is
// whether the run returned everything it borrowed.
//
// The two cases below differ only in the source, so the priming, the run and
// both expectations are stated once here. Both name their variable `x`, since
// what the caller varies is which of §11.5.1's two routes into a select that
// addresses no bit the source takes, not what the target is called.
static void ExpectSelectNbaWritesNothingAndKeepsItsEvent(const std::string& src,
                                                         SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  auto& pool = f.scheduler.GetEventPool();
  constexpr size_t kPrimedEvents = 32;
  std::vector<Event*> primed;
  primed.reserve(kPrimedEvents);
  for (size_t n = 0; n < kPrimedEvents; ++n) primed.push_back(pool.Acquire());
  for (auto* e : primed) pool.Release(e);
  ASSERT_EQ(pool.FreeCount(), kPrimedEvents);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // §11.5.1's "no effect on the data stored when written": no bit of x moved.
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 0x00u);
  // Every event the run took from the primed stock came back to it.
  EXPECT_EQ(pool.FreeCount(), kPrimedEvents);
}

// §4.9.4 has a nonblocking assignment compute "the left-hand target" from "the
// values in effect when the update is placed in the event region", so the index
// of a select target is resolved where the update is scheduled. §11.5.1 leaves
// that resolution nothing to write when the index carries x -- "a part-select
// that is x or z shall yield the value x when read and shall have no effect on
// the data stored when written", and its bullet list has
// `vect[expression that returns x]` return x -- so the update is dropped and
// `x` keeps the 8'h00 the blocking write left. `i` is never assigned, so it
// holds 3'bxxx: §6.11.2 makes `logic` one of the 4-state types, "types that can
// have unknown and high-impedance values", and §6.8's Table 6-7 -- "the default
// values for variables if no initializer is specified" -- gives a 4-state
// integral variable 'x.
//
// Dropping the write is what the clause asks for; abandoning the event taken to
// carry it is not. The scheduling path acquires an Event from the pool before
// it knows whether the select addresses any bit, and only an event that reaches
// a queue is ever released (Scheduler::DrainQueue), so the one taken here left
// the pool for good -- the Arena has no per-object free to reclaim it, and a
// long-running design drops one event per such assignment. It handed back 31 of
// the 32 the helper primes.
TEST(NonblockingAssignSchedulingSim,
     DroppedUnknownIndexSelectNbaReturnsItsEvent) {
  SimFixture f;
  ExpectSelectNbaWritesNothingAndKeepsItsEvent(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [2:0] i;\n"
      "  initial begin\n"
      "    x = 8'h00;\n"
      "    x[i] <= 1'b1;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
}

// The same abandonment reached by the other of §11.5.1's two routes into a
// select that addresses no bit of its object: not an index carrying x, but "a
// part-select that addresses a range of bits that are completely out of the
// address bounds of the vector", which `x[9:8]` on a `logic [7:0] x` is -- both
// of its indices sit above the declared 7. The clause gives it the same
// treatment, "no effect on the data stored when written", so `x` keeps 8'h00,
// and the same event goes with it. The two are worth having separately because
// they reach the drop through different arithmetic: the first stops at the
// unknown-bits test on the evaluated index, this one at the range test in
// PartSelectStorageBits, and only the shared zero width they both answer with
// tells the scheduling path there is nothing to place. This one also returned
// 31 of 32.
TEST(NonblockingAssignSchedulingSim,
     DroppedOutOfRangePartSelectNbaReturnsItsEvent) {
  SimFixture f;
  ExpectSelectNbaWritesNothingAndKeepsItsEvent(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'h00;\n"
      "    x[9:8] <= 2'b11;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
}

// §4.9.4 requires "the values in effect when the update is placed in the event
// region" to compute "both the right-hand value and the left-hand target", and
// §10.4.2 spells the target half out: "if the variable_lvalue requires an
// evaluation, such as an index expression, class handle, or virtual interface
// reference, it shall be evaluated at the same time as the expression on the
// right-hand side". Nothing in either sentence exempts an lvalue that is a
// concatenation: the index expressions inside its elements are part of the
// left-hand target, so `idx` is read where the `<=` executes and not where the
// deferred update runs.
//
// `idx` is 0 at that point, so the top bit of the 9-bit right-hand side -- a 1
// -- belongs in `a[0]`, leaving a at 8'h01, and the remaining eight bits give b
// 8'h55. Re-reading `idx` in the update region finds the 3 written after the
// statement and puts the bit in `a[3]`, i.e. 8'h08; scheduling nothing at all
// leaves the 8'h00 the blocking write put there. The three outcomes are
// distinct, so this case cannot pass by accident. `b` reads 8'h55 under all
// three, which is what confines the failure to the element carrying the index.
TEST(NonblockingAssignSchedulingSim,
     LhsConcatBitSelectTargetUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int idx;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    b = 8'h00;\n"
      "    idx = 0;\n"
      "    {a[idx], b} <= 9'b1_0101_0101;\n"
      "    idx = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  // Bit 0, the index in effect when the update was placed -- not bit 3.
  EXPECT_EQ(va->value.ToUint64(), 0x01u);
  EXPECT_EQ(vb->value.ToUint64(), 0x55u);
}

// The same rule over the other kind of evaluation a concatenation element can
// carry: an indexed part-select, whose §11.5.1 offset `idx` is an ordinary
// index expression and so falls under the same §10.4.2 sentence as the
// bit-select above. Splitting the two is worth it because the deferred lvalue
// stores an offset and a width here rather than a single bit position, and a
// snapshot that keeps only the offset would still slide the window.
//
// With `idx` 0 the target is `a[3:0]`, which takes the top nibble C of the
// 12-bit right-hand side, and `b` takes the low byte 5A. An offset re-read in
// the update region is 4, putting C in `a[7:4]` for 8'hC0. The `b` value is
// what pins the element width as well as the offset: `a[idx +: 4]` contributes
// exactly four bits to the concatenation regardless of where the window sits,
// so a slice that had moved or resized would cut b's byte at a different place
// and 8'h5A would not survive. The trailing check reads `idx` itself, so a run
// that somehow never executed the statement after the `<=` is told apart from
// one that executed it at the right time.
TEST(NonblockingAssignSchedulingSim,
     LhsConcatPartSelectOffsetUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int idx;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    b = 8'h00;\n"
      "    idx = 0;\n"
      "    {a[idx +: 4], b} <= 12'hC5A;\n"
      "    idx = 4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* target = f.ctx.FindVariable("a");
  ASSERT_NE(target, nullptr);
  // a[3:0], the window in effect at scheduling -- not the a[7:4] of 8'hC0.
  EXPECT_EQ(target->value.ToUint64(), 0x0Cu);
  auto* rest = f.ctx.FindVariable("b");
  ASSERT_NE(rest, nullptr);
  EXPECT_EQ(rest->value.ToUint64(), 0x5Au);
  auto* offset = f.ctx.FindVariable("idx");
  ASSERT_NE(offset, nullptr);
  // The statement after the `<=` did run; it just came too late to be read.
  EXPECT_EQ(offset->value.ToUint64(), 4u);
}

// The streaming half of the same rule. §11.4.14 makes a streaming concatenation
// a legal variable_lvalue, and the with-range of §11.4.14.4 -- Syntax 11-5's
// array_range_expression -- is an index expression inside it, so §10.4.2 has it
// "evaluated at the same time as the expression on the right-hand side" like
// any other. This is the only shape in which the streaming arm's deferral is
// observable: a plain element there names its object outright and never reads
// an index, so the with-range is the one place a later write to `idx` has
// anything to move.
//
// `idx` is 0 when the update is placed, so `arr with [0 +: 2]` is elements 0
// and 1, and a right-shift stream lays 16'hABCD into them in order. Re-reading
// `idx` in the update region finds 2 and lands AB and CD in `arr[2]` and
// `arr[3]` instead. The two untouched elements are checked as well as the two
// written ones, since only the pair of zeros says the bytes went to elements 0
// and 1 rather than also reaching the far end of the array.
TEST(NonblockingAssignSchedulingSim,
     LhsStreamingConcatWithRangeUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  int idx;\n"
      "  initial begin\n"
      "    idx = 0;\n"
      "    {>> {arr with [idx +: 2]}} <= 16'hABCD;\n"
      "    idx = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  const std::pair<const char*, uint64_t> kWanted[] = {
      {"arr[0]", 0xABu}, {"arr[1]", 0xCDu}, {"arr[2]", 0u}, {"arr[3]", 0u}};
  for (const auto& [name, wanted] : kWanted) {
    auto* element = f.ctx.FindVariable(name);
    ASSERT_NE(element, nullptr) << "Variable not found: " << name;
    EXPECT_EQ(element->value.ToUint64(), wanted) << "Variable: " << name;
  }
}
