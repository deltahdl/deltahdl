#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §3.14.1 governs how a delay value is rounded to a design element's time
// precision before it is used in simulation. The rule is observed end to end:
// each test drives real source (a delay control whose element carries a
// timeunit/timeprecision declaration, §3.14.2.2) through parse, elaborate, and
// run, then reads the advanced simulation time the rounded delay produced.

// When the precision equals the time unit, a fractional delay is rounded to a
// whole number of time units. With the default 1 ns unit and 1 ns precision, a
// 2.75 ns delay rounds up to 3, so $time (an integer scaled to the module unit)
// reads 3 rather than the truncated 2.
TEST(DesignBuildingBlockSimulation, SamePrecisionRoundsFractionalDelayUp) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer x;\n"
                      "  initial begin\n"
                      "    #2.75 x = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            3u);
}

// Same-precision rounding also rounds down: 2.3 ns rounds to 2.
TEST(DesignBuildingBlockSimulation, SamePrecisionRoundsFractionalDelayDown) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer x;\n"
                      "  initial begin\n"
                      "    #2.3 x = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            2u);
}

// A tie rounds away from zero, matching the LRM's round-half-up description:
// 2.5 ns rounds to 3.
TEST(DesignBuildingBlockSimulation, SamePrecisionRoundsHalfAwayFromZero) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer x;\n"
                      "  initial begin\n"
                      "    #2.5 x = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            3u);
}

// When the precision is one order of magnitude smaller than the unit, one
// fractional digit survives: with a 1 ns unit and 100 ps precision, 2.75 ns
// rounds to 2.8 ns. $realtime keeps the fractional module-unit value, so it
// reads 2.8 -- the exact example from §3.14.1.
TEST(DesignBuildingBlockSimulation, OneOrderSmallerKeepsOneDecimal) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("module t;\n"
                                 "  timeunit 1ns / 100ps;\n"
                                 "  real x;\n"
                                 "  initial begin\n"
                                 "    #2.75 x = $realtime;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x"),
                   2.8);
}

// The same 100 ps precision rounds 2.73 ns down to 2.7 ns.
TEST(DesignBuildingBlockSimulation, OneOrderSmallerRoundsDown) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("module t;\n"
                                 "  timeunit 1ns / 100ps;\n"
                                 "  real x;\n"
                                 "  initial begin\n"
                                 "    #2.73 x = $realtime;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x"),
                   2.7);
}

// A delay is held to its own element's precision even when a finer precision
// exists elsewhere in the design. Here t declares 100 ps precision while the
// instantiated child declares 1 ps, so the shared (global) tick base is 1 ps
// and could represent 2.756 ns exactly. The rule still rounds t's delay to its
// own 100 ps step, giving 2.8 ns rather than 2.756 ns.
TEST(DesignBuildingBlockSimulation, DelayHeldToOwnElementPrecision) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("module sub;\n"
                                 "  timeunit 1ns / 1ps;\n"
                                 "endmodule\n"
                                 "module t;\n"
                                 "  timeunit 1ns / 100ps;\n"
                                 "  sub s();\n"
                                 "  real x;\n"
                                 "  initial begin\n"
                                 "    #2.756 x = $realtime;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x"),
                   2.8);
}

// The rounding rule reaches the intra-assignment delay of a blocking
// assignment too (§10.4.1): x = #2.75 1 completes at the rounded time 3, so a
// following read of $time sees 3.
TEST(DesignBuildingBlockSimulation, IntraAssignmentDelayRounds) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer x;\n"
                      "  initial begin\n"
                      "    x = #2.75 1;\n"
                      "    x = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            3u);
}

// An integer delay has no fractional part to round and passes through
// unchanged, confirming the rounding path does not perturb whole delays.
TEST(DesignBuildingBlockSimulation, IntegerDelayIsUnchanged) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer x;\n"
                      "  initial begin\n"
                      "    #5 x = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            5u);
}

// The rounding applies to a delay whose value is produced at run time by a
// variable read rather than a literal -- a distinct evaluation path for the
// delay operand. Default 1 ns precision rounds the 2.75 held in d up to 3.
TEST(DesignBuildingBlockSimulation, VariableSourcedFractionalDelayRounds) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer x;\n"
                      "  real d;\n"
                      "  initial begin\n"
                      "    d = 2.75;\n"
                      "    #d x = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            3u);
}

// When the precision is two orders of magnitude smaller than the unit, two
// fractional digits survive: with a 1 ns unit and 10 ps precision, 2.756 ns
// rounds to 2.76 ns.
TEST(DesignBuildingBlockSimulation, TwoOrdersSmallerKeepsTwoDecimals) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("module t;\n"
                                 "  timeunit 1ns / 10ps;\n"
                                 "  real x;\n"
                                 "  initial begin\n"
                                 "    #2.756 x = $realtime;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x"),
                   2.76);
}

// A delay that is already an exact multiple of the element's precision step is
// left unchanged -- the boundary where rounding is a no-op. Under 100 ps
// precision, 2.8 ns is exactly 28 steps and stays 2.8 ns.
TEST(DesignBuildingBlockSimulation, ExactPrecisionMultipleUnchanged) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("module t;\n"
                                 "  timeunit 1ns / 100ps;\n"
                                 "  real x;\n"
                                 "  initial begin\n"
                                 "    #2.8 x = $realtime;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x"),
                   2.8);
}

}  // namespace
