#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
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

CoverCounts CoverRun(const std::string& before, const std::string& items) {
  SimFixture f;
  RunAndFindVar(before +
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
                    "  property p(y, z); y |-> z; endproperty\n" +
                    items +
                    "  initial #60 $finish;\n"
                    "endmodule\n",
                f, "tick");
  f.ctx.RunFinalBlocks();
  const auto& results = f.ctx.ConcurrentCovers().Results();
  if (results.size() != 1) return {};
  return {results[0].attempted, results[0].succeeded, results[0].vacuous};
}

CoverCounts Cover(const std::string& property) {
  return CoverRun("",
                  "  cv: cover property (@(posedge clk) " + property + ");\n");
}

struct CoverRow {
  const char* property;
  uint64_t succeeded;
  uint64_t vacuous;
};

void ExpectCounts(const CoverCounts& counts, uint64_t succeeded,
                  uint64_t vacuous) {
  EXPECT_EQ(counts.attempted, 6u);
  EXPECT_EQ(counts.succeeded, succeeded);
  EXPECT_EQ(counts.vacuous, vacuous);
}

void ExpectEachRow(std::initializer_list<CoverRow> rows) {
  for (const CoverRow& row : rows) {
    SCOPED_TRACE(row.property);
    ExpectCounts(Cover(row.property), row.succeeded, row.vacuous);
  }
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

TEST(NonvacuousEvaluationRun,
     AStrongOrWeakMultiCycleSequenceIsAlwaysNonvacuous) {
  ExpectEachRow({{"strong(a ##1 b)", 1, 0}, {"weak(a ##1 b)", 1, 0}});
}

TEST(NonvacuousEvaluationRun, DISABLED_AStrongOrWeakBooleanIsAlwaysNonvacuous) {
  ExpectEachRow({{"strong(c)", 3, 0}, {"weak(c)", 3, 0}});
}

TEST(NonvacuousEvaluationRun, AnAndIsNonvacuousWhereEitherOperandIs) {
  ExpectEachRow({{"(a |-> b) and (en |-> c)", 4, 1}});
}

TEST(NonvacuousEvaluationRun,
     AnIfWithoutElseIsVacuousWhereItsConditionIsFalse) {
  ExpectEachRow({{"if (en) (a |-> b)", 1, 5}});
}

TEST(NonvacuousEvaluationRun, AnImplicationWithAVacuousConsequentIsVacuous) {
  ExpectEachRow({{"c |-> (a |-> b)", 1, 5}, {"c |=> (a |-> b)", 1, 4}});
}

TEST(NonvacuousEvaluationRun, AnInstanceIsAsNonvacuousAsItsSubstitutedBody) {
  ExpectEachRow({{"p(a, b)", 2, 3}});
}

TEST(NonvacuousEvaluationRun,
     AFollowedByNeedsAnAntecedentMatchAndANonvacuousConsequent) {
  ExpectEachRow({{"c #-# (a |-> b)", 1, 2}, {"c #=# (a |-> b)", 1, 1}});
}

TEST(NonvacuousEvaluationRun,
     ACountedOrStrongNexttimeNeedsItsTickAndANonvacuousAttempt) {
  ExpectEachRow({{"nexttime [2] (a |-> b)", 1, 4},
                 {"s_nexttime (a |-> b)", 2, 2},
                 {"s_nexttime [2] (a |-> b)", 1, 2}});
}

TEST(NonvacuousEvaluationRun,
     AnUnboundedOrStrongAlwaysNeedsANonvacuousTickAndNoPriorFailure) {
  ExpectEachRow(
      {{"always (a |-> b)", 1, 1}, {"s_always [0:1] (en |-> c)", 3, 2}});
}

TEST(NonvacuousEvaluationRun, AnEventuallyNeedsANonvacuousTickAndNoPriorHold) {
  ExpectEachRow({{"s_eventually (a |-> b)", 3, 3},
                 {"s_eventually [1:2] (a |-> b)", 3, 2},
                 {"eventually [1:2] (a |-> b)", 3, 3}});
}

TEST(NonvacuousEvaluationRun, AnUntilIsWitnessedByEitherOperand) {
  ExpectEachRow({{"(en |-> c) until (x |-> a)", 4, 2},
                 {"(en |-> c) s_until (x |-> a)", 4, 2}});
}

TEST(NonvacuousEvaluationRun, AnUntilWithIsWitnessedByItsLeftOperandAlone) {
  ExpectEachRow({{"(en |-> c) until_with (x |-> a)", 3, 3},
                 {"(en |-> c) s_until_with (x |-> a)", 3, 3}});
}

TEST(NonvacuousEvaluationRun,
     AnImpliesIsNonvacuousOnlyOverATrueNonvacuousAntecedent) {
  ExpectEachRow({{"c implies b", 1, 3}, {"c implies (a |-> b)", 1, 5}});
}

TEST(NonvacuousEvaluationRun,
     DISABLED_AnImpliesOverAVacuouslyTrueAntecedentIsVacuous) {
  ExpectEachRow({{"(en |-> c) implies b", 1, 1},
                 {"(en |-> c) implies (a |-> b)", 1, 4},
                 {"(a |-> b) implies (en |-> c)", 1, 5},
                 {"(en |-> 0) implies (a |-> b)", 0, 5},
                 {"(en |-> c) implies (a |-> b) or 0", 3, 2},
                 {"p(en, c) implies b", 1, 1}});
}

TEST(NonvacuousEvaluationRun, AnIffIsNonvacuousWhereEitherOperandIs) {
  ExpectEachRow({{"(en |-> c) iff (a |-> b)", 4, 1}});
}

TEST(NonvacuousEvaluationRun,
     ARejectOrSyncAbortNeedsANonvacuousOperandAndNoAbort) {
  ExpectEachRow({{"reject_on (x) (c |=> en)", 2, 2},
                 {"sync_accept_on (x) (c |=> en)", 2, 4},
                 {"sync_reject_on (x) (c |=> en)", 2, 2}});
}

TEST(NonvacuousEvaluationRun, ACaseIsAsNonvacuousAsTheItemItSelects) {
  ExpectEachRow({{"case (en) 1'b1: (a |-> b); default: c; endcase", 1, 2},
                 {"case (en) 1'b1: (a |-> b); endcase", 1, 5}});
}

TEST(NonvacuousEvaluationRun, ADisableIffNeedsANonvacuousOperandAndNoDisable) {
  ExpectEachRow({{"disable iff (x) (c |=> en)", 2, 2}});
}

TEST(NonvacuousEvaluationRun, AProceduralCoverCountsVacuousSuccessesApart) {
  ExpectCounts(CoverRun("",
                        "  always @(posedge clk) begin\n"
                        "    cv: cover property (a |-> b);\n"
                        "  end\n"),
               2, 3);
}

TEST(NonvacuousEvaluationRun, ACheckersCoverCountsVacuousSuccessesApart) {
  ExpectCounts(CoverRun("checker ck(logic clk, logic a, logic b);\n"
                        "  cv: cover property (@(posedge clk) a |-> b);\n"
                        "endchecker\n",
                        "  ck u(clk, a, b);\n"),
               2, 3);
}

}  // namespace
