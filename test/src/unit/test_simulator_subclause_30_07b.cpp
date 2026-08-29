// §30.7's pulse filtering as a running simulation performs it: a pulse is
// driven through a module path and the value that came out the far side is read
// off what the run printed.
//
// §30.7 deems two consecutive transitions scheduled on a module path output
// closer together in time than the module path delay a pulse, and gives the
// verdict to the reject and error limits belonging to the delay forming the
// pulse's trailing edge -- at or above the error limit it propagates, at or
// above the reject limit it is filtered to x, and below the reject limit it is
// rejected and no pulse emerges. Every case below elaborates, lowers and runs a
// design whose output carries such a pulse and asserts on the two lines the run
// printed. That is the one arrangement test_simulator_subclause_30_07a.cpp
// cannot make fail: that file calls ClassifyPulse from
// src/simulator/specify_path_delay.h itself, so it proves the classifier
// answers correctly and not that anything asks it. Issue #3266 is exactly that
// gap -- the limits were computed and then consulted by nothing, because no
// §30.4 module path delay reached the driver of a module path output.
//
// Every design here is Figure 30-5's, whose caption is this file's subject:
// `(a => y) = (7, 9);` over a buffer, a 4-wide pulse on `a`, and the 2-wide
// pulse that reaches `y` because the fall delay 9 and the rise delay 7 differ
// by 2. `y` rises at t=7, the pulse's leading edge is scheduled for t=29 and
// its trailing edge for t=31, so a sample at t=30 falls inside the pulse and
// one at t=35 falls after it. The two samples together are what tell the three
// outcomes apart, and neither does so alone: a rejected pulse leaves `y` at 1
// at both, a filtered one reads x then 1, and a propagating one reads 0 then 1.
// The limits that decide are Table 30-2 slot 0's, the rising trailing edge's,
// and not slot 1's, which the falling leading edge would answer to.
//
// The literals are picked so that no two quantities a case tells apart share a
// value. The rise delay 7 and the fall delay 9 differ from each other, from the
// pulse width 2 they produce, and from the limit 3 that a case sets to reject
// that width. The pulse width 2 meets the reject limit 2 exactly where §30.7's
// "greater than or equal to the reject limit" boundary is the claim being made.
// The pair PulseAtErrorLimitPropagatesToOutput and
// SamePulseIsRejectedByNarrowerLimit differ in one PATHPULSE$ value and in
// nothing else, so what they tell apart is the limits rather than the delays.
//
// Each PATHPULSE$ value is parenthesized -- `= (2, 9)` and not the standard's
// own `= 2,9` -- because Parser::ParseSpecparamInSpecify in
// src/parser/parser_specify.cpp follows Syntax 30-7 and requires the
// parentheses. Issue #3384 covers the unparenthesised form being rejected.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Figure 30-5's stimulus: `a` sits at 1, drops for 4 time units, and returns.
// The 4-wide pulse on `a` is what the 9 and the 7 narrow to 2 at `y`.
constexpr std::string_view kPulseStimulus =
    "    s = 1'b1;\n"
    "    #20 s = 1'b0;\n"
    "    #4 s = 1'b1;\n";

// The same stimulus with `s` held at 0 for 20 rather than 4. `y` falls at t=29
// and rises at t=47, which are 18 apart and so further apart than either delay:
// §30.7 deems this no pulse, and no limit is consulted for it.
constexpr std::string_view kNoPulseStimulus =
    "    s = 1'b1;\n"
    "    #20 s = 1'b0;\n"
    "    #20 s = 1'b1;\n";

// Figure 30-5's buffer with `extra_specify_item` added to its specify block,
// `stimulus` driving its input, and `y` displayed at the two times given.
//
// The module is the top module of its source because only a top module's
// specify block is registered, which issue #3383 records. Each sample prints
// `at<time>=<value>`, so the time a value was read at is part of the line the
// case asserts on rather than something the reader has to count.
//
// `a` is an input port and `s` the variable the stimulus writes, because
// §30.4.1 rules that a module path source "shall be a net" connected to an
// input or inout port, and CheckSpecifyPathTerminal in
// src/elaborator/elaborator_validate_specify.cpp rejects a path source that is
// a local signal. An input port has no driver in a top module, so `assign a =
// s;` supplies one: §23.3.3.3 admits a continuous assignment onto a net input
// port, and ValidateInputPortAssignments in
// src/elaborator/elaborator_validate_matches.cpp passes it for that reason.
// The extra assignment costs a delta cycle and no simulation time, so every
// time below is the time `s` moved.
std::string PulseDesign(std::string_view extra_specify_item,
                        std::string_view stimulus, int first_sample,
                        int second_sample) {
  std::string first = std::to_string(first_sample);
  std::string second = std::to_string(second_sample);
  return std::string(
             "module t(input a, output y);\n"
             "  logic s;\n"
             "  assign a = s;\n"
             "  assign y = a;\n"
             "  specify\n"
             "    (a => y) = (7, 9);\n") +
         std::string(extra_specify_item) +
         "  endspecify\n"
         "  initial begin\n" +
         std::string(stimulus) +
         "  end\n"
         "  initial #" +
         first + " $display(\"at" + first + "=%b\", y);\n" + "  initial #" +
         second + " $display(\"at" + second + "=%b\", y);\n" + "endmodule\n";
}

// §30.7: with no PATHPULSE$ specparam, both limits of a module path transition
// delay are set equal to that delay, so the rise delay 7 rejects the 2-wide
// pulse. This is Figure 30-5's own outcome: waveform Y never moves, and `y`
// holds the 1 it took at t=7 across both samples.
TEST(ModulePathPulseFiltering, PulseBelowRejectLimitNeverReachesOutput) {
  SimFixture f;
  std::string out = RunCapture(PulseDesign("", kPulseStimulus, 30, 35), f);
  EXPECT_EQ(out, "at30=1\nat35=1\n");
}

// §30.7: transitions further apart than the module path delay are not a pulse,
// so nothing is filtered and both edges reach `y`. This is what says the
// rejection above is filtering rather than a path that carries nothing: the
// same design with the same delays moves `y` when the transitions are 18 apart.
TEST(ModulePathPulseFiltering, TransitionsWiderThanDelayAreNotAPulse) {
  SimFixture f;
  std::string out = RunCapture(PulseDesign("", kNoPulseStimulus, 35, 50), f);
  EXPECT_EQ(out, "at35=0\nat50=1\n");
}

// §30.7: a pulse at or above the reject limit but below the error limit is
// filtered to a logic x at the path destination. Reject 2 and error 9 put the
// 2-wide pulse in that range, so `y` reads x inside the pulse and takes the
// trailing edge's 1 after it.
TEST(ModulePathPulseFiltering, PulseAtRejectLimitBelowErrorLimitDrivesX) {
  SimFixture f;
  std::string out =
      RunCapture(PulseDesign("    specparam PATHPULSE$a$y = (2, 9);\n",
                             kPulseStimulus, 30, 35),
                 f);
  EXPECT_EQ(out, "at30=x\nat35=1\n");
}

// §30.7: a pulse at or above the error limit propagates to the path
// destination unfiltered. Reject 2 and error 2 put the 2-wide pulse at the
// error limit, so both of its edges appear on `y`: 0 inside the pulse and 1
// after it.
TEST(ModulePathPulseFiltering, PulseAtErrorLimitPropagatesToOutput) {
  SimFixture f;
  std::string out =
      RunCapture(PulseDesign("    specparam PATHPULSE$a$y = (2, 2);\n",
                             kPulseStimulus, 30, 35),
                 f);
  EXPECT_EQ(out, "at30=0\nat35=1\n");
}

// §30.7: the same pulse, the same delays, and one wider reject limit. Raising
// the limits from 2 to 3 puts the 2-wide pulse below the reject limit, so it is
// rejected and `y` never moves. This case and
// PulseAtErrorLimitPropagatesToOutput differ in that one specparam value alone,
// which is what ties the outcome to the pulse limits rather than to the
// transition delays they were derived from.
TEST(ModulePathPulseFiltering, SamePulseIsRejectedByNarrowerLimit) {
  SimFixture f;
  std::string out =
      RunCapture(PulseDesign("    specparam PATHPULSE$a$y = (3, 3);\n",
                             kPulseStimulus, 30, 35),
                 f);
  EXPECT_EQ(out, "at30=1\nat35=1\n");
}

}  // namespace
