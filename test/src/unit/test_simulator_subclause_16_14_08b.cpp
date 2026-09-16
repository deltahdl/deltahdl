#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/cover_results.h"

using namespace delta;

namespace {

// A module around the cover statement given, as
// test/src/e2e/nonvacuous_evaluations.sv is: clk rises at 5, 15, ..., 55,
// tick n at 10n - 5; a is high at ticks 2, 4 and 5, b at 2 and 5, c and en
// at 1 to 3 and x at 4; the run ends at 60. The cover's results at the end
// count its successes and the vacuous ones among them.
struct CoverCounts {
  uint64_t attempted = 0;
  uint64_t succeeded = 0;
  uint64_t vacuous = 0;
};

CoverCounts Cover(const std::string& property) {
  SimFixture f;
  RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  int tick = 1;\n"
      "  logic a, b, c, en, x;\n"
      "  always #5 clk = ~clk;\n"
      "  always #10 tick = tick + 1;\n"
      "  assign a = tick inside {2, 4, 5};\n"
      "  assign b = tick inside {2, 5};\n"
      "  assign c = tick inside {1, 2, 3};\n"
      "  assign en = tick inside {1, 2, 3};\n"
      "  assign x = tick inside {4};\n"
      "  c: cover property (@(posedge clk) " +
          property +
          ");\n"
          "  initial #60 $finish;\n"
          "endmodule\n",
      f, "tick");
  f.ctx.RunFinalBlocks();
  const auto& results = f.ctx.ConcurrentCovers().Results();
  if (results.size() != 1) return {};
  return {results[0].attempted, results[0].succeeded, results[0].vacuous};
}

// §16.14.8 (a) and (d): a boolean's attempt is a sequence's, nonvacuous
// always, and not p's is p's, so not (a |-> b) succeeds once, at 4, and
// nonvacuously, the implication's consequent having begun there.
TEST(NonvacuousEvaluationRun, ANegationIsAsNonvacuousAsItsOperand) {
  CoverCounts counts = Cover("not (a |-> b)");
  EXPECT_EQ(counts.attempted, 6u);
  EXPECT_EQ(counts.succeeded, 1u);
  EXPECT_EQ(counts.vacuous, 0u);
}

// §16.14.8 (e): an or is nonvacuous where either operand's attempt is, and
// c's attempt is a sequence's, so (a |-> b) or c never succeeds vacuously
// though the implication does at 1, 3 and 6.
TEST(NonvacuousEvaluationRun, AnOrIsNonvacuousWhereEitherOperandIs) {
  CoverCounts counts = Cover("(a |-> b) or c");
  EXPECT_EQ(counts.attempted, 6u);
  EXPECT_EQ(counts.succeeded, 5u);
  EXPECT_EQ(counts.vacuous, 0u);
}

// §16.14.8 (g): an if takes the branch its condition selects: the
// implication at 1 to 3, vacuous at 1 and 3 and nonvacuous at 2, and c at 4
// to 6, where it fails.
TEST(NonvacuousEvaluationRun, AnIfIsAsNonvacuousAsTheBranchTaken) {
  CoverCounts counts = Cover("if (en) a |-> b else c");
  EXPECT_EQ(counts.attempted, 6u);
  EXPECT_EQ(counts.succeeded, 3u);
  EXPECT_EQ(counts.vacuous, 2u);
}

// §16.14.8 (l): a nexttime is nonvacuous where there was a next clock event
// and the attempt beginning there is: nonvacuous from 1 and 4, vacuous from
// 2 and 5, and vacuous from 6, whose next tick the run never reaches.
TEST(NonvacuousEvaluationRun, ANexttimeNeedsANextTickAndANonvacuousAttempt) {
  CoverCounts counts = Cover("nexttime (a |-> b)");
  EXPECT_EQ(counts.attempted, 6u);
  EXPECT_EQ(counts.succeeded, 5u);
  EXPECT_EQ(counts.vacuous, 3u);
}

// §16.14.8 (q): an always over a range is nonvacuous where a tick of the
// range has a nonvacuous attempt and the operand fails at no tick before:
// nonvacuous from 1, 2 and 5, failing from 3 and 4, and vacuous from 6,
// whose second tick the run never reaches.
TEST(NonvacuousEvaluationRun, AnAlwaysNeedsANonvacuousTickAndNoPriorFailure) {
  CoverCounts counts = Cover("always [0:1] (a |-> b)");
  EXPECT_EQ(counts.attempted, 6u);
  EXPECT_EQ(counts.succeeded, 4u);
  EXPECT_EQ(counts.vacuous, 1u);
}

// §16.14.8 (ab): an accept_on is nonvacuous where its operand's attempt is
// and its condition held at no time step of the attempt: the attempts from
// 1, 3 and 6 hold vacuously, a being low, the attempt from 4 is accepted by
// x and holds vacuously too, and those from 2 and 5 fail.
TEST(NonvacuousEvaluationRun, AnAcceptedAttemptIsVacuous) {
  CoverCounts counts = Cover("accept_on (x) (a |=> b)");
  EXPECT_EQ(counts.attempted, 6u);
  EXPECT_EQ(counts.succeeded, 4u);
  EXPECT_EQ(counts.vacuous, 4u);
}

}  // namespace
