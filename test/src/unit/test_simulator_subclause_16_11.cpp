#include <gtest/gtest.h>

#include <string>

#include "elaborator/sequence_match_attach.h"
#include "fixture_simulator.h"
#include "helpers_sequence_ticks.h"

using namespace delta;

namespace {

TEST(AttachedSubroutineScheduling, RegionIsReactive) {
  // §16.11: attached subroutine calls are scheduled in the Reactive region,
  // exactly like an action block.
  EXPECT_EQ(AttachedSubroutineRegion(),
            AttachedSubroutineSchedulingRegion::kReactive);
}

TEST(AttachedSubroutineScheduling, EvaluationDoesNotAwaitCallReturn) {
  // §16.11: assertion evaluation does not wait on, or receive data back
  // from, any attached subroutine.
  EXPECT_FALSE(AssertionEvalWaitsForAttachedSubroutine());
}

TEST(AttachedSubroutineScheduling, ByValueArgumentUsesSampledValues) {
  // §16.11: an actual argument passed by value reads the sampled value of
  // the underlying variable rather than its current value.
  EXPECT_TRUE(ByValueArgumentUsesSampledValuesOfUnderlying());
}

TEST(AttachedSubroutineScheduling, ByValueArgumentMatchesSequenceEvaluation) {
  // §16.11: the sampled value used for a by-value argument is consistent
  // with the value used to evaluate the sequence match it is attached to.
  EXPECT_TRUE(ByValueArgumentValueIsConsistentWithSequenceMatch());
}

// --- Live cases: the linear sequence monitor over real source ---
//
// The shared source finishes at 160, which the capture ends with.

// §16.11: the clause's s1 over te1 as a and te2 as b, with v and w assigned
// from te3 and te4: the attached $display runs at the match, at the first te2
// strictly after te1, writing the locals as assigned. te1 at tick 1 with te3
// high and te2 at 3 with te4 low print v as 1 and w as 0 at the tick at 25.
TEST(AttachedSubroutine, RunsAtTheMatchWithTheLocalsAssigned) {
  SimFixture f;
  std::string out = RunCapture(
      SequenceTickSource(
          "(te1, v = te3) ##1 (te2[->1], w = te4, $display(\"b after a with v "
          "= %h, w = %h at %0t\", v, w, $time))",
          DriveTicks({{1}, {3}, {1}, {}, {}}), "", "    logic v, w;\n"),
      f);
  EXPECT_EQ(out, "b after a with v = 1, w = 0 at 25\n$finish at time 160\n");
}

// §16.11: the attached calls are executed at every end point of the
// sequence, in the order they appear in the list. `te1 ##[1:2] te2` with te1
// at 1 and te2 at 2 and 3 ends at 2 and at 3, and both calls run at each.
TEST(AttachedSubroutine, RunsAtEveryEndPointInListOrder) {
  SimFixture f;
  std::string out = RunCapture(
      SequenceTickSource("(te1 ##[1:2] te2, $display(\"first at %0t\", $time), "
                         "$display(\"second at %0t\", $time))",
                         DriveTicks({{1}, {2, 3}, {}, {}, {}})),
      f);
  EXPECT_EQ(out,
            "first at 15\nsecond at 15\nfirst at 25\nsecond at 25\n"
            "$finish at time 160\n");
}

// §16.11: an argument passed by value reads the sampled value the sequence
// match used, though the call runs in the Reactive region, after the
// nonblocking assignments of the time step: k counts the clock's edges
// through a nonblocking assignment, so at the tick at 25, the third edge, the
// match reads k as 2 while k reads 3 by the time the call runs.
TEST(AttachedSubroutine, ByValueArgumentReadsTheSampledValue) {
  SimFixture f;
  std::string out =
      RunCapture(SequenceTickSource("(te1, $display(\"k = %0d\", k))",
                                    DriveTicks({{3}, {}, {}, {}, {}}),
                                    "  int k = 0;\n"
                                    "  always @(posedge clk) k <= k + 1;\n"),
                 f);
  EXPECT_EQ(out, "k = 2\n$finish at time 160\n");
}

// §16.11: a void function is called as a system task is, its by-value
// argument the sampled value.
TEST(AttachedSubroutine, VoidFunctionIsCalledAtTheMatch) {
  SimFixture f;
  std::string out =
      RunCapture(SequenceTickSource("(te1 ##1 te2, note($time))",
                                    DriveTicks({{2}, {3}, {}, {}, {}}),
                                    "  function void note(int t);\n"
                                    "    $display(\"noted %0d\", t);\n"
                                    "  endfunction\n"),
                 f);
  EXPECT_EQ(out, "noted 25\n$finish at time 160\n");
}

}  // namespace
