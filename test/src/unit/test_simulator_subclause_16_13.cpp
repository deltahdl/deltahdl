#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The design of test/src/e2e/multiclock_sequences.sv around one assertion:
// clk0 rises at 5, 15, ..., 75 so that tick n of it is at 10n - 5, clk1 at
// 12, 27, 45, 57 and 72, its tick at 45 together with clk0's fifth; sig0
// is high at 1, 2, 5 and 7 and sig1 at 3 and 5.
std::string MulticlockSource(const std::string& items) {
  return "module t;\n"
         "  logic clk0 = 0;\n"
         "  logic clk1 = 0;\n"
         "  int tick = 1;\n"
         "  logic sig0, sig1;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  int last_pass = 0;\n"
         "  always #5 clk0 = ~clk0;\n"
         "  always #10 tick = tick + 1;\n"
         "  initial begin\n"
         "    #12 clk1 = 1;\n"
         "    #8 clk1 = 0;\n"
         "    #7 clk1 = 1;\n"
         "    #8 clk1 = 0;\n"
         "    #10 clk1 = 1;\n"
         "    #5 clk1 = 0;\n"
         "    #7 clk1 = 1;\n"
         "    #8 clk1 = 0;\n"
         "    #7 clk1 = 1;\n"
         "    #6 clk1 = 0;\n"
         "  end\n"
         "  assign sig0 = tick inside {1, 2, 5, 7};\n"
         "  assign sig1 = tick inside {3, 5};\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

// The pass and fail counts of the assertion over `spec`, clocked on clk0,
// and the time of its last pass.
struct MulticlockCounts {
  uint64_t passes;
  uint64_t fails;
  uint64_t last_pass;
};

MulticlockCounts CountsOfMulticlock(const std::string& spec) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      MulticlockSource("  p: assert property (@(posedge clk0) " + spec +
                       ") begin passes++; last_pass = $time; end "
                       "else fails++;\n"),
      f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  Variable* last_pass = f.ctx.FindVariable("last_pass");
  return {passes->value.ToUint64(), fails->value.ToUint64(),
          last_pass->value.ToUint64()};
}

// §16.13.1: ##1 between subsequences on different clocks moves from the
// end point of the first, at a tick of clk0, to the nearest strictly
// subsequent tick of clk1: the attempt from 15 holds at 27, the one from
// 45 fails at 57, the next tick of clk1 after 45, and the six others fail.
TEST(MulticlockSequences, ASingleDelayMovesToTheNextTickOfTheSecondClock) {
  MulticlockCounts counts = CountsOfMulticlock("sig0 ##1 @(posedge clk1) sig1");
  EXPECT_EQ(counts.passes, 1u);
  EXPECT_EQ(counts.fails, 7u);
  EXPECT_EQ(counts.last_pass, 27u);
}

// §16.13.1: ##0 moves to the nearest possibly overlapping tick of clk1,
// which is clk1's tick at 45 for the attempt from 45, where sig1 holds, and
// the next tick of clk1 otherwise, as ##1 does.
TEST(MulticlockSequences, AZeroDelayMovesToTheOverlappingTickWhereThereIsOne) {
  MulticlockCounts counts = CountsOfMulticlock("sig0 ##0 @(posedge clk1) sig1");
  EXPECT_EQ(counts.passes, 2u);
  EXPECT_EQ(counts.fails, 6u);
  EXPECT_EQ(counts.last_pass, 45u);
}

// §16.13.1: where the clocks are identical the clocking event does not
// change, and the sequence is the singly clocked sig0 ##1 sig1, which reads
// sig1 a tick of clk0 after sig0 and holds from 15 alone, at 25.
TEST(MulticlockSequences, TheSameClockNamedAgainChangesNothing) {
  MulticlockCounts counts = CountsOfMulticlock("sig0 ##1 @(posedge clk0) sig1");
  EXPECT_EQ(counts.passes, 1u);
  EXPECT_EQ(counts.fails, 7u);
  EXPECT_EQ(counts.last_pass, 25u);
  MulticlockCounts plain = CountsOfMulticlock("sig0 ##1 sig1");
  EXPECT_EQ(plain.passes, 1u);
  EXPECT_EQ(plain.fails, 7u);
  EXPECT_EQ(plain.last_pass, 25u);
}

// §16.13.1 with §9.4 Syntax 9-4: `@clk1` and `@(clk1)` are one clocking event,
// every change of clk1, at 12, 20, 27, 35, 45, 50, 57, 65, 72 and 78. Of the
// attempts where sig0 holds, from 5, 15, 45 and 65, only the one from 45 finds
// sig1 at the next change, 50; the bare form is read and evaluated as the
// parenthesised one is.
TEST(MulticlockSequences, ABareNamedClockIsTheParenthesisedOnesEvent) {
  MulticlockCounts paren = CountsOfMulticlock("sig0 ##1 @(clk1) sig1");
  EXPECT_EQ(paren.passes, 1u);
  EXPECT_EQ(paren.fails, 7u);
  EXPECT_EQ(paren.last_pass, 50u);
  MulticlockCounts bare = CountsOfMulticlock("sig0 ##1 @clk1 sig1");
  EXPECT_EQ(bare.passes, 1u);
  EXPECT_EQ(bare.fails, 7u);
  EXPECT_EQ(bare.last_pass, 50u);
}

// §16.13.1 with §15.5.1: a named event is a clock of a multiclocked sequence as
// an edge of a signal is, each trigger a tick. ne is triggered at every fall
// of clk and nclk is ~clk, so @(ne) and @(posedge nclk) tick at the same
// instants, and a sequence gives the same matches on either, whether the
// event clocks its second subsequence or its first.
std::string EventClockSource(const std::string& second_clock,
                             const std::string& leading_clock) {
  return "module t;\n"
         "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
         "  logic nclk; assign nclk = ~clk;\n"
         "  bit [0:9] av = 10'b1010010000, bv = 10'b0110011010;\n"
         "  bit a, b; assign a = av[0]; assign b = bv[0];\n"
         "  always @(negedge clk) av <= av << 1;\n"
         "  always @(posedge clk) bv <= bv << 1;\n"
         "  event ne; always @(negedge clk) -> ne;\n"
         "  int second = 0, leading = 0;\n"
         "  cover property (@(posedge clk) a ##1 @(" +
         second_clock +
         ") b) second++;\n"
         "  cover property (@(" +
         leading_clock +
         ") b ##1 @(posedge clk) a) leading++;\n"
         "endmodule\n";
}

TEST(MulticlockSequences, ANamedEventClocksASubsequenceAsASignalEdgeDoes) {
  SimFixture f;
  auto* second = RunAndFindVar(EventClockSource("ne", "ne"), f, "second");
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(second->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("leading")->value.ToUint64(), 2u);
  SimFixture g;
  auto* edge = RunAndFindVar(EventClockSource("posedge nclk", "posedge nclk"),
                             g, "second");
  ASSERT_NE(edge, nullptr);
  EXPECT_EQ(edge->value.ToUint64(), 2u);
  EXPECT_EQ(g.ctx.FindVariable("leading")->value.ToUint64(), 2u);
}

// §16.13.1 with §16.14.5: an attempt begins at a tick of the leading clock
// alone. nclk is ~clk and rises at 0, from x to 1, before clk has risen at
// all; the cover's ten attempts begin at clk's rises at 5, 15, ..., 95 and
// each matches at the next rise of nclk, 10, 20, ..., 100, where an attempt
// begun at 0 would match at 10 as well.
TEST(MulticlockSequences, AnotherClockTickingFirstBeginsNoAttempt) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  logic nclk; assign nclk = ~clk;\n"
      "  bit a = 1, b = 1;\n"
      "  int hits = 0;\n"
      "  cover property (@(posedge clk) a ##1 @(posedge nclk) b) hits++;\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 10u);
}

// §16.13.1 with §23.6: a clock of a multiclocked sequence whose signal is
// named by a path, `@(negedge i0.clk)` through an interface instance bound to
// clk, ticks as the clock written over clk does, so the two covers match
// equally often.
TEST(MulticlockSequences, AClockNamedByAPathTicksAsItsSignalDoes) {
  SimFixture f;
  auto* path = RunAndFindVar(
      "interface ifc(input logic clk);\n"
      "endinterface\n"
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1101001111;\n"
      "  bit [0:19] bv = 20'b01101001011101000110;\n"
      "  always @(posedge clk) av <= av << 1;\n"
      "  always @(clk) bv <= bv << 1;\n"
      "  bit a, b; assign a = av[0]; assign b = bv[0];\n"
      "  ifc i0(clk);\n"
      "  int c1 = 0, c2 = 0;\n"
      "  cover property (@(posedge clk) a ##1 @(negedge i0.clk) b) c1++;\n"
      "  cover property (@(posedge clk) a ##1 @(negedge clk) b) c2++;\n"
      "endmodule\n",
      f, "c1");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("c2")->value.ToUint64(), 4u);
}

// §16.14.5 with §16.13.1: an assertion on an instance of a property whose
// body names a second clock begins its attempts at its leading clock alone.
// The interface's port clk falls from x at 0, a tick of the second clock
// before the leading clock has risen, and no attempt begins there, so the
// instance fails as often as the same property declared in the module.
TEST(MulticlockSequences, AnInstancesSecondClockTickingFirstBeginsNoAttempt) {
  SimFixture f;
  auto* fi = RunAndFindVar(
      "interface ifc(input logic clk);\n"
      "  logic a, b;\n"
      "  property p_clk; @(posedge clk) a ##1 @(negedge clk) b; endproperty\n"
      "endinterface\n"
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1101001111, bv = 10'b0110011110;\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  logic a, b; assign a = av[0]; assign b = bv[0];\n"
      "  ifc i0(clk);\n"
      "  assign i0.a = a; assign i0.b = b;\n"
      "  property m_clk; @(posedge clk) a ##1 @(negedge clk) b; endproperty\n"
      "  int fi = 0, fm = 0;\n"
      "  assert property (i0.p_clk) else fi++;\n"
      "  assert property (m_clk) else fm++;\n"
      "endmodule\n",
      f, "fi");
  ASSERT_NE(fi, nullptr);
  EXPECT_EQ(fi->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("fm")->value.ToUint64(), 5u);
}

// The same for an instance with actuals, whose body's sequence the actuals
// are substituted into: clk falls from x at 0, a tick of the property's second
// clock before its leading clock has risen, and the instance fails as often as
// the sequence written into the assertion.
TEST(MulticlockSequences,
     AnInstanceWithActualsBeginsNoAttemptAtItsSecondClock) {
  SimFixture f;
  auto* fi = RunAndFindVar(
      "module t;\n"
      "  logic clk; initial begin clk = 0; repeat (20) #5 clk = ~clk; end\n"
      "  bit [0:9] av = 10'b1101001111, bv = 10'b0110011110;\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  logic a, b; assign a = av[0]; assign b = bv[0];\n"
      "  property pm(x, y); @(posedge clk) x ##1 @(negedge clk) y; "
      "endproperty\n"
      "  int fi = 0, fm = 0;\n"
      "  assert property (pm(a, b)) else fi++;\n"
      "  assert property (@(posedge clk) a ##1 @(negedge clk) b) else fm++;\n"
      "endmodule\n",
      f, "fi");
  ASSERT_NE(fi, nullptr);
  EXPECT_EQ(fi->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("fm")->value.ToUint64(), 6u);
}

}  // namespace
