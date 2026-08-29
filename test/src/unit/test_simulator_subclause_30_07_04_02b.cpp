// §30.7.4.2's negative pulse as a running simulation shows it: Figure 30-7's
// design is elaborated, lowered and run, and the value that appeared at the
// module path output is read off what the run printed.
//
// §30.7.4.2 rules that when unequal delays schedule a pulse's trailing edge
// earlier than its leading edge the pulse has a negative width, and that under
// normal operation the leading edge is cancelled, "leaving no indication a
// schedule was ever present". The showcancelled style of behavior instead
// schedules the leading edge to x and the trailing edge from x, and §30.7.4.1's
// pulse style decides when that x begins: on-event replaces the leading edge
// schedule, on-detect makes the schedule to x "immediately upon detection of
// the negative pulse". Every case below drives that source through the full
// parse/elaborate/lower/run pipeline and asserts on the three lines the run
// printed. That is the one arrangement
// test_simulator_subclause_30_07_04_02a.cpp cannot make fail: that file hands
// ScheduleNegativePulse and IsNegativePulse a mode, a style and two times as
// arguments, so it proves those functions answer correctly and not that a run
// ever asks them. That gap is issue 3386 exactly: a negative pulse on a module
// path output was always cancelled, so showcancelled showed nothing.
//
// Every design here is Figure 30-7's with its times doubled. The figure's own
// numbers put the on-event x between t=15 and t=16, adjacent integers with no
// time strictly inside them, so no sample could distinguish that x from its
// absence. Doubling every delay and every stimulus time preserves each
// relationship the figure states and opens the x wide enough to sample.
//
// The literals follow from that doubling. The rise delay 8 and the fall delay
// 12 are the figure's 4 and 6; they differ from each other, and their
// difference of 4 is the width of the on-event x. The stimulus times 20 and 22
// are the figure's 10 and 11: `in` falls at 20, which schedules `out`'s 1->0
// transition through the fall delay 12 for t=32, and `in` rises at 22, which
// schedules `out`'s 0->1 transition through the rise delay 8 for t=30. 30 is
// earlier than 32, so the pulse is negative and is detected at t=22. The x
// therefore spans 30..32 under on-event and 22..32 under on-detect. The samples
// 25, 31 and 40 are each strictly inside or strictly outside both regions: 25
// is inside the on-detect x and outside the on-event x, 31 is inside both, and
// 40 is after both. No two of the four cases agree on all three samples.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Figure 30-7's buffer at doubled times, with `extra_specify_item` inserted
// into its specify block ahead of the module path declaration, and `out`
// displayed at t=25, t=31 and t=40. Each sample prints `at<time>=<value>`, so
// the time a value was read at is part of the line the case asserts on.
//
// The extra item precedes the path declaration because
// ValidatePulseStyleConflicts in src/elaborator/elaborator_validate_specify.cpp
// reports a showcancelled or pulsestyle declaration naming an output that an
// earlier path declaration in the same block already drives.
//
// `in` is an input port and `s` the variable the stimulus writes, because
// §30.4.1 rules that a module path source shall be a net connected to a module
// input or inout port, and CheckSpecifyPathTerminal in the same source rejects
// a path terminal that is a declared local signal. An input port of a top
// module has no driver, so `assign in = s;` supplies one: §23.3.3.3 admits a
// continuous assignment onto a net input port. That assignment costs a delta
// cycle and no simulation time, so every time below is the time `s` moved. The
// module is the last in the source because ElaborateSrc in
// lib/cpp/test_fixtures/fixture_simulator.h elaborates the last one.
std::string NegativePulseDesign(std::string_view extra_specify_item) {
  std::string source = "module t(input in, output out);\n";
  source += "  logic s;\n";
  source += "  assign in = s;\n";
  source += "  assign out = in;\n";
  source += "  specify\n";
  source += extra_specify_item;
  source += "    (in => out) = (8, 12);\n";
  source += "  endspecify\n";
  source += "  initial begin\n";
  source += "    s = 1'b1;\n";
  source += "    #20 s = 1'b0;\n";
  source += "    #2 s = 1'b1;\n";
  source += "  end\n";
  source += "  initial #25 $display(\"at25=%b\", out);\n";
  source += "  initial #31 $display(\"at31=%b\", out);\n";
  source += "  initial #40 $display(\"at40=%b\", out);\n";
  source += "endmodule\n";
  return source;
}

// §30.7.4.2: under normal operation the leading edge of a negative pulse is
// cancelled, and because the initial and final states of the pulse are the
// same no transition takes place, "leaving no indication a schedule was ever
// present". `out` settles at 1 before t=20 and reads 1 at all three samples,
// which is Figure 30-7's own out (default) waveform.
TEST(NegativePulseAtOutput, DefaultModeShowsNothingOfTheNegativePulse) {
  SimFixture f;
  std::string out = RunCapture(NegativePulseDesign(""), f);
  EXPECT_EQ(out, "at25=1\nat31=1\nat40=1\n");
}

// §30.7.4.2: noshowcancelled selects the normal operation the case above gets
// by default. Declaring it explicitly reads the same three 1s, which is what
// says the mode is answering rather than the declaration going unread: the
// same source with showcancelled in its place moves `out`.
TEST(NegativePulseAtOutput, ExplicitNoshowcancelledShowsNothingEither) {
  SimFixture f;
  std::string out =
      RunCapture(NegativePulseDesign("    noshowcancelled out;\n"), f);
  EXPECT_EQ(out, "at25=1\nat31=1\nat40=1\n");
}

// §30.7.4.2: showcancelled schedules the leading edge of a negative pulse to x
// and the trailing edge from x, and with the default on-event pulse style "the
// schedule to X replaces the leading edge schedule". The leading edge stood at
// t=30 and the trailing at t=32, so `out` is x across 30..32: 1 at t=25, which
// is before the x begins, x at t=31, and 1 again at t=40. This is Figure
// 30-7's out (showcancelled with on-event) waveform at doubled times.
TEST(NegativePulseAtOutput, ShowcancelledOnEventDrivesXFromLeadingSchedule) {
  SimFixture f;
  std::string out =
      RunCapture(NegativePulseDesign("    showcancelled out;\n"), f);
  EXPECT_EQ(out, "at25=1\nat31=x\nat40=1\n");
}

// §30.7.4.2: with the on-detect pulse style "the schedule to X is made
// immediately upon detection of the negative pulse". The pulse is detected at
// t=22, when the rising input schedules the trailing edge earlier than the
// leading one, so `out` is x across 22..32 and reads x at t=25 as well as at
// t=31. This case and ShowcancelledOnEventDrivesXFromLeadingSchedule differ in
// the pulsestyle_ondetect declaration alone, so what the t=25 sample tells
// apart is the pulse style rather than the delays or the stimulus. This is
// Figure 30-7's out (showcancelled with on-detect) waveform at doubled times.
TEST(NegativePulseAtOutput, ShowcancelledOnDetectDrivesXFromDetection) {
  SimFixture f;
  std::string out =
      RunCapture(NegativePulseDesign("    showcancelled out;\n"
                                     "    pulsestyle_ondetect out;\n"),
                 f);
  EXPECT_EQ(out, "at25=x\nat31=x\nat40=1\n");
}

}  // namespace
