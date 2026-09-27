#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

// §30.6: when a module mixes a module path delay and distributed delays along
// that path, the larger of the two shall be used. The rule is a two-operand
// maximum, so its only distinguishable behaviors are "module path delay wins"
// and "distributed sum wins" — the two worked examples in the clause exercise
// exactly those outcomes.

// LRM Example 1 (Figure 30-3): module path delay 22 exceeds the distributed
// sum 0 + 1 = 1, so the module path delay is used.
TEST(MixedPathDistributedDelay, ModulePathLargerWinsLrmExample1) {
  EXPECT_EQ(SelectEffectivePathDelay(22, 1), 22u);
}

// LRM Example 2 (Figure 30-4): the distributed sum 10 + 20 = 30 exceeds the
// module path delay 22, so the distributed sum is used.
TEST(MixedPathDistributedDelay, DistributedSumLargerWinsLrmExample2) {
  EXPECT_EQ(SelectEffectivePathDelay(22, 30), 30u);
}

// Boundary between the two winning outcomes: when the module path delay and the
// distributed sum are equal, "the larger of the two" resolves to that shared
// value rather than doubling or otherwise combining them.
TEST(MixedPathDistributedDelay, EqualDelaysYieldThatValue) {
  EXPECT_EQ(SelectEffectivePathDelay(22, 22), 22u);
}

// Negative of the mixing precondition (path delay present, no distributed
// delays along the path): the distributed sum is zero, so the module path delay
// is used unchanged. The clause's rule only mixes when both kinds are present.
TEST(MixedPathDistributedDelay, NoDistributedDelayUsesModulePath) {
  EXPECT_EQ(SelectEffectivePathDelay(22, 0), 22u);
}

// Negative of the mixing precondition in the other direction (distributed
// delays present, no module path delay): the module path delay is zero, so the
// distributed sum is used unchanged.
TEST(MixedPathDistributedDelay, NoModulePathUsesDistributedDelay) {
  EXPECT_EQ(SelectEffectivePathDelay(0, 30), 30u);
}

// Figure 30-3 of §30.6 (printed page 885) run: the cell's d reaches q through
// an `and #0` and an `or` of delay `or_delay`, and its module path from d to q
// is 22, d rising at 40 and falling at 80.
std::string Figure30Dash3Cell(const std::string& or_delay) {
  return "module mycell(input a, input b, input c, input d, output q);\n"
         "  wire w1, w2;\n"
         "  and #0 (w1, a, b);\n"
         "  and #0 (w2, c, d);\n"
         "  or #" +
         or_delay +
         " (q, w1, w2);\n"
         "  specify\n"
         "    (d *> q) = 22;\n"
         "  endspecify\n"
         "endmodule\n"
         "module top;\n"
         "  logic a, b, c, d;\n"
         "  wire tq;\n"
         "  mycell u(.a(a), .b(b), .c(c), .d(d), .q(tq));\n"
         "  always @(tq) if ($time > 0) $display(\"t=%0t q=%b\", $time, tq);\n"
         "  initial begin\n"
         "    a = 0; b = 0; c = 1; d = 0;\n"
         "    #40 d = 1;\n"
         "    #40 d = 0;\n"
         "  end\n"
         "endmodule\n";
}

// "a transition on Q caused by a transition on D will occur 22 time units after
// the transition on D": the gates' 0 + 1 is the smaller of the two, so q
// follows d by 22. The path delay reached only an output a continuous
// assignment drove, and q followed d by the gates' 1 alone.
TEST(MixedPathDistributedDelayRun, ModulePathLargerWinsOverGates) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Figure30Dash3Cell("1"), f),
            "t=22 q=0\nt=62 q=1\nt=102 q=0\n");
}

// The other way round: with an `or #30` the gates' 30 is the larger of the two
// and q follows d by 30.
TEST(MixedPathDistributedDelayRun, GatesLargerWinOverModulePath) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Figure30Dash3Cell("30"), f),
            "t=30 q=0\nt=70 q=1\nt=110 q=0\n");
}

// §30.6 (printed page 885) with a continuous assignment's own delay the larger:
// `assign #10` beside `(a => y) = 4` moves y 10 after a. y stayed x.
TEST(MixedPathDistributedDelayRun, AssignmentDelayLargerWinsOverModulePath) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module mybuf(input a, output y);\n"
                       "  assign #10 y = a;\n"
                       "  specify\n"
                       "    (a => y) = 4;\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic a; wire ty;\n"
                       "  mybuf u(.a(a), .y(ty));\n"
                       "  always @(ty) if ($time >= 12) $display(\"t=%0t "
                       "y=%b\", $time, ty);\n"
                       "  initial begin\n"
                       "    a = 0;\n"
                       "    #10 a = 1;\n"
                       "    #10 a = 0;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=20 y=1\nt=30 y=0\n");
}

}  // namespace
