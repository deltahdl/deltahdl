#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/cover_results.h"

using namespace delta;

namespace {

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
      "  cv: cover property (@(posedge clk) " +
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

TEST(NonvacuousEvaluationRun, ANegationIsAsNonvacuousAsItsOperand) {
  CoverCounts counts = Cover("not (a |-> b)");
  EXPECT_EQ(counts.attempted, 6u);
  EXPECT_EQ(counts.succeeded, 1u);
  EXPECT_EQ(counts.vacuous, 0u);
}

TEST(NonvacuousEvaluationRun, AnOrIsNonvacuousWhereEitherOperandIs) {
  CoverCounts counts = Cover("(a |-> b) or c");
  EXPECT_EQ(counts.attempted, 6u);
  EXPECT_EQ(counts.succeeded, 5u);
  EXPECT_EQ(counts.vacuous, 0u);
}

TEST(NonvacuousEvaluationRun, AnIfIsAsNonvacuousAsTheBranchTaken) {
  CoverCounts counts = Cover("if (en) a |-> b else c");
  EXPECT_EQ(counts.attempted, 6u);
  EXPECT_EQ(counts.succeeded, 1u);
  EXPECT_EQ(counts.vacuous, 2u);
}

TEST(NonvacuousEvaluationRun, ANexttimeNeedsANextTickAndANonvacuousAttempt) {
  CoverCounts counts = Cover("nexttime (a |-> b)");
  EXPECT_EQ(counts.attempted, 6u);
  EXPECT_EQ(counts.succeeded, 2u);
  EXPECT_EQ(counts.vacuous, 3u);
}

TEST(NonvacuousEvaluationRun, AnAlwaysNeedsANonvacuousTickAndNoPriorFailure) {
  CoverCounts counts = Cover("always [0:1] (a |-> b)");
  EXPECT_EQ(counts.attempted, 6u);
  EXPECT_EQ(counts.succeeded, 3u);
  EXPECT_EQ(counts.vacuous, 1u);
}

TEST(NonvacuousEvaluationRun, AnAcceptedAttemptIsVacuous) {
  CoverCounts counts = Cover("accept_on (x) (a |=> b)");
  EXPECT_EQ(counts.attempted, 6u);
  EXPECT_EQ(counts.succeeded, 0u);
  EXPECT_EQ(counts.vacuous, 4u);
}

}  // namespace
