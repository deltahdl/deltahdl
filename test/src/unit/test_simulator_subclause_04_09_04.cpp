#include <gtest/gtest.h>

#include <cstddef>
#include <string>
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
