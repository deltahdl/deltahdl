// The order §30.5.3 applies its two activity tests in, which decides whether an
// output that is plainly transitioning takes a module path delay at all.
//
// §30.5.3 states both tests in one sentence: "Active specify paths are those
// whose input has transitioned most recently in time, and either they have no
// condition or their conditions are true." Taking the transition time first
// lets a path whose condition is false set the most recent time and drop every
// path with a true condition standing at an earlier one, so nothing is selected
// and the output takes no module path delay while a live path stood ready to
// govern it. Taking the condition first leaves the most recent time to be taken
// among the paths that are eligible at all, and the live path governs. Issue
// #3393 is that gap. The three cases below are about that order and about
// nothing else.
//
// No file beside this one can ask the question.
// test/src/unit/test_simulator_subclause_30_05_03a.cpp calls SelectPathDelay
// and hands it both quantities as arguments, but every candidate it builds
// holds one of the two fixed: its Example 1 and specparam cases pass
// PathCandidate::condition_true as `true` on every candidate and vary only the
// transition times, and its Example 2 cases pass the same transition time on
// all five candidates and vary only the conditions. A case has to vary both at
// once for the order to be observable.
// test/src/unit/test_simulator_subclause_30_05_03b.cpp does drive a design, but
// the §30.5.3 Example 1 paths it drives carry no condition at all, so every
// candidate it builds is active whichever test runs first.
// test/src/unit/test_simulator_subclause_30_05_03c.cpp drives conditions, but
// all five of its §30.5.3 Example 2 paths share the single source `a`, so every
// candidate it builds carries one transition time and no path can displace
// another on time.
//
// The design under the second and third cases is two state-dependent paths that
// reach one output from different sources, which is the smallest design in
// which the two tests can disagree:
//
//     if (sel)  (a => y) = 6;
//     if (!sel) (b => y) = 4;
//
// `b` rises at t=20 and `a` at t=50, so `a` is the source that transitioned
// most recently and `sel` decides whether the path from it is live. With `sel`
// low that path's condition is false and the live path stands at the earlier
// time, which is the case that fails when the time is taken first. With `sel`
// high the live path is the one that also moved last, so the two tests agree
// and the case passes whichever order is applied; it is what says the condition
// selects the path rather than one answer being handed to both.
//
// The first case is here rather than in
// test/src/unit/test_simulator_subclause_30_05_03a.cpp because it makes the
// same claim as the two below it at the one stage that decides it:
// SelectActivePath returns the path that governs, and the case names which of
// two candidates that is. Reading it beside the run-driven pair is what shows
// the design's answer following from the selection rule rather than from
// anything else in the path between a stimulus and an output.
//
// Every quantity a case tells apart has a value of its own. `y` reaches 1 at
// t=54 with `sel` low, at t=56 with `sel` high, and at t=50 under the order
// this file rejects, where no path is selected and §30.6 leaves `assign y = a &
// b;` its own distributed delay of zero. Those three times are distinct, so
// neither case's answer is a time the other case or the defect could have
// produced. The time is read off an `always @(y)` rather than off a sample
// because a sample states only which side of itself a transition fell on; the
// header of test/src/unit/test_simulator_subclause_30_05_03b.cpp records that
// reason at length. The samples at t=48 and t=60 straddle all three times and
// fall on none of them, so neither reads `y` in a time slot it is being written
// in.
//
// `a & b` drives `y` because it holds `y` at 0 until the second of the two
// inputs rises, which is what makes `a` at t=50 the input that carries `y` up
// while `b` at t=20 is the input whose path governs the move. Under `a | b` the
// first input to rise would carry `y` with it at t=20 and the transition under
// test would not happen at all.
//
// `sel` is a locally declared variable rather than a parameter because
// §30.4.4.1 lists a locally defined variable among the operands a
// state-dependent path condition may name, and CheckConditionExpr in
// src/elaborator/elaborator_validate_specify_limits.cpp accepts it: a bare
// identifier that is not an output port passes, and `!` is one of the logical
// operators Table 30-1 permits. A relational operator is not, which is why the
// conditions are written this way rather than as §30.5.3's own examples print
// them.
//
// `armed` exists because `y` leaves its initial x within the first six time
// units, at a moment the delays §30.5.2 derives for the x slots decide and no
// case here is about. It is raised at t=40, after that settling and before the
// one stimulus edge that matters, so the run prints one transition line and it
// belongs to the case.
//
// `a` and `b` are input ports and `y` an output port because §30.4.1 requires a
// module path source to be a net connected to an input or inout port and a
// destination to be connected to an output or inout port, and
// CheckSpecifyPathTerminal in src/elaborator/elaborator_validate_specify.cpp
// rejects a path terminal that is a declared local signal. An input port of a
// top module has no driver, so `sa` and `sb` supply one through `assign a =
// sa;`, which §23.3.3.3 admits onto a net input port and which costs a delta
// cycle and no simulation time. Every time below is therefore the time `sa` or
// `sb` was written.

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

constexpr uint8_t kRiseSlot = 0;  // 0 -> 1 column of Table 30-2.

// A module path from `src_port` to `y` whose one declared delay is `ticks`,
// spread over all twelve transition slots the way §30.5.1 spreads a single
// value. The two paths the first case compares differ in their source and in
// that delay and in nothing else, so which of them SelectActivePath returns is
// the whole of what the case states.
PathDelay OneDelayPath(std::string_view src_port, uint64_t ticks) {
  PathDelay pd;
  pd.src_port = std::string(src_port);
  pd.dst_port = "y";
  pd.delay_count = 1;
  pd.delays[0] = ticks;
  ExpandTransitionDelays(pd);
  return pd;
}

// The two-path design above with `sel` set to `sel_value`, which is what each
// run-driven case varies and all it varies.
//
// `sb` rises at t=20 and `sa` at t=50, so `a` is the source that moved most
// recently and `sel` decides whether the path from it is live. The `always
// @(y)` names the time `y` followed, which is the answer the case asserts, and
// the samples at t=48 and t=60 corroborate it by reporting `y` low before every
// candidate time and high after all of them.
//
// The module is the only one in the source and so the one ElaborateSrc
// elaborates, and it is a top module because only a top module's specify block
// is registered, which issue #3383 records.
std::string ConditionRaceSource(std::string_view sel_value) {
  std::string src = R"(module dut(input a, b, output y);
  logic sa, sb, armed, sel;
  assign a = sa;
  assign b = sb;
  assign y = a & b;
  specify
    if (sel) (a => y) = 6;
    if (!sel) (b => y) = 4;
  endspecify
  always @(y) begin
    if (armed) $display("y=%b t=%0d", y, $time);
  end
  initial begin
    sel = )";
  src.append(sel_value);
  src += R"(;
    armed = 1'b0;
    sa = 1'b0;
    sb = 1'b0;
    #20 sb = 1'b1;
    #20 armed = 1'b1;
    #10 sa = 1'b1;
  end
  initial #48 $display("at 48 y=%b", y);
  initial #60 $display("at 60 y=%b", y);
endmodule
)";
  return src;
}

// §30.5.3 asks for the paths "whose input has transitioned most recently in
// time, and either they have no condition or their conditions are true", and
// the candidate at t=50 answers the first half while failing the second. The
// path whose condition holds transitioned at t=20, so it is the most recent
// among the candidates that are eligible at all and it is what governs. Taking
// the time over every candidate first makes t=50 the mark, drops the candidate
// at t=20 for not standing at it, and returns no path.
TEST(ModulePathActivityOrder,
     AnInactiveLaterPathLeavesTheEarlierLiveOneActive) {
  PathDelay disabled = OneDelayPath("a", 6);
  PathDelay live = OneDelayPath("b", 4);
  std::vector<PathCandidate> candidates = {{&disabled, 50, false},
                                           {&live, 20, true}};
  EXPECT_EQ(SelectActivePath(candidates, kRiseSlot), &live);
}

// With `sel` low, `if (!sel) (b => y) = 4;` is the live path and its source
// moved at t=20, while the source of the disabled `if (sel) (a => y) = 6;`
// moved at t=50 and carried `y` up with it. The live path governs, so `y`
// reaches 1 at t=54. Under the order this file rejects no path is selected at
// all, §30.6 leaves the transition the zero distributed delay of `assign y = a
// & b;`, and `y` reaches 1 at t=50 instead.
TEST(ModulePathActivityOrder, ADisabledLastInputLeavesTheLivePathGoverning) {
  SimFixture f;
  std::string out = RunCapture(ConditionRaceSource("1'b0"), f);
  EXPECT_EQ(out, "at 48 y=0\ny=1 t=54\nat 60 y=1\n");
}

// With `sel` high the live path is `if (sel) (a => y) = 6;`, whose source is
// also the one that moved most recently, so both of §30.5.3's tests pick it and
// their order cannot matter. `y` reaches 1 at t=56. The design differs from the
// case above in the value of `sel` alone, so the two answers differing is the
// condition choosing which path governs rather than one delay being handed to
// every run.
TEST(ModulePathActivityOrder, AnEnabledLastInputTakesItsOwnPathDelay) {
  SimFixture f;
  std::string out = RunCapture(ConditionRaceSource("1'b1"), f);
  EXPECT_EQ(out, "at 48 y=0\ny=1 t=56\nat 60 y=1\n");
}

}  // namespace
