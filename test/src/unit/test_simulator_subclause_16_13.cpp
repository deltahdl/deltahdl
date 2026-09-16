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

}  // namespace
