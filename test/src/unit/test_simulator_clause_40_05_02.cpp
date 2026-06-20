// Tests for IEEE 1800-2023 Clause 40.5.2 "Obtaining coverage information".
//
// This subclause has no grammar; it describes what a PLI client reads back
// through vpi_get() for the coverage properties of §40.5.1. Each test observes
// a production helper deriving a reported coverage figure from raw simulator
// tallies, mirroring the corresponding vpi_get() property.

#include <gtest/gtest.h>

#include <cstdint>
#include <optional>

#include "simulator/vpi_coverage.h"

namespace delta {
namespace {

// C4: vpiAssertAttemptCovered reports the number of attempts.
TEST(CoverageInformationQueries, AttemptCoveredReportsAttempts) {
  AssertionCoverageCounters c;
  c.attempts = 7;
  EXPECT_EQ(AssertAttemptCovered(c), 7U);
}

// C5: vpiAssertSuccessCovered reports nonvacuous successes, or, for a cover
// sequence handle, the number of matches.
TEST(CoverageInformationQueries, SuccessCoveredReportsNonvacuousSuccesses) {
  AssertionCoverageCounters c;
  c.successes = 4;
  EXPECT_EQ(AssertSuccessCovered(c), 4U);

  AssertionCoverageCounters seq;
  seq.is_cover_sequence = true;
  seq.successes = 9;  // matches of the cover sequence
  EXPECT_EQ(AssertSuccessCovered(seq), 9U);
}

// C6: vpiAssertVacuousSuccessCovered reports vacuous successes.
TEST(CoverageInformationQueries, VacuousSuccessCoveredReportsVacuousSuccesses) {
  AssertionCoverageCounters c;
  c.vacuous_successes = 3;
  EXPECT_EQ(AssertVacuousSuccessCovered(c), 3U);
}

// C7: vpiAssertDisableCovered reports times the disabled state was reached.
TEST(CoverageInformationQueries, DisableCoveredReportsDisabledCount) {
  AssertionCoverageCounters c;
  c.disabled = 2;
  EXPECT_EQ(AssertDisableCovered(c), 2U);
}

// C8: vpiAssertKillCovered reports times the assertion was killed.
TEST(CoverageInformationQueries, KillCoveredReportsKilledCount) {
  AssertionCoverageCounters c;
  c.killed = 5;
  EXPECT_EQ(AssertKillCovered(c), 5U);
}

// C9: vpiAssertFailureCovered reports failures.
TEST(CoverageInformationQueries, FailureCoveredReportsFailures) {
  AssertionCoverageCounters c;
  c.failures = 6;
  EXPECT_EQ(AssertFailureCovered(c), 6U);
}

// C1 + C4-C9: the dispatch from a §40.5.1 assertion-status property to its
// reported count returns the right tally for each property and 0 for a
// non-assertion-status property.
TEST(CoverageInformationQueries, StatusQueryDispatchesByProperty) {
  AssertionCoverageCounters c;
  c.attempts = 10;
  c.successes = 4;
  c.vacuous_successes = 1;
  c.disabled = 2;
  c.killed = 1;
  c.failures = 2;

  EXPECT_EQ(AssertionStatusQuery(CoverageProperty::kAssertAttemptCovered, c),
            10U);
  EXPECT_EQ(AssertionStatusQuery(CoverageProperty::kAssertSuccessCovered, c),
            4U);
  EXPECT_EQ(
      AssertionStatusQuery(CoverageProperty::kAssertVacuousSuccessCovered, c),
      1U);
  EXPECT_EQ(AssertionStatusQuery(CoverageProperty::kAssertDisableCovered, c),
            2U);
  EXPECT_EQ(AssertionStatusQuery(CoverageProperty::kAssertKillCovered, c), 1U);
  EXPECT_EQ(AssertionStatusQuery(CoverageProperty::kAssertFailureCovered, c),
            2U);
  // A property that is not an assertion-status count contributes nothing.
  EXPECT_EQ(AssertionStatusQuery(CoverageProperty::kStatementCoverage, c), 0U);
}

// C3: vpiCovered on an assertion is true only when the assertion has been
// attempted, has succeeded nonvacuously, and has never failed.
TEST(CoverageInformationQueries,
     AssertionCoveredRequiresAttemptSuccessNoFailure) {
  AssertionCoverageCounters covered;
  covered.attempts = 3;
  covered.successes = 3;
  EXPECT_TRUE(AssertionCovered(covered));

  AssertionCoverageCounters never_attempted;
  EXPECT_FALSE(AssertionCovered(never_attempted));

  AssertionCoverageCounters no_success;
  no_success.attempts = 3;
  EXPECT_FALSE(AssertionCovered(no_success));

  AssertionCoverageCounters has_failed;
  has_failed.attempts = 3;
  has_failed.successes = 2;
  has_failed.failures = 1;
  EXPECT_FALSE(AssertionCovered(has_failed));
}

// C3 (edge): only nonvacuous successes count toward coverage. An assertion that
// has been attempted and has only ever succeeded vacuously is not covered.
TEST(CoverageInformationQueries, AssertionCoveredExcludesVacuousOnlySuccess) {
  AssertionCoverageCounters vacuous_only;
  vacuous_only.attempts = 4;
  vacuous_only.vacuous_successes = 4;
  EXPECT_FALSE(AssertionCovered(vacuous_only));
}

// C12: Table 40-3 worked example for anvr, aundf, afail, apass.
TEST(CoverageInformationQueries, WorkedExampleAssertionCoverageResults) {
  // anvr: never attempted.
  AssertionCoverageCounters anvr;
  EXPECT_FALSE(AssertionCovered(anvr));
  EXPECT_EQ(AssertAttemptCovered(anvr), 0U);
  EXPECT_EQ(AssertSuccessCovered(anvr), 0U);
  EXPECT_EQ(AssertFailureCovered(anvr), 0U);

  // aundf: attempted but never passes or fails.
  AssertionCoverageCounters aundf;
  aundf.attempts = 5;
  EXPECT_FALSE(AssertionCovered(aundf));
  EXPECT_GT(AssertAttemptCovered(aundf), 0U);
  EXPECT_EQ(AssertSuccessCovered(aundf), 0U);
  EXPECT_EQ(AssertFailureCovered(aundf), 0U);

  // afail: attempted, fails.
  AssertionCoverageCounters afail;
  afail.attempts = 5;
  afail.failures = 5;
  EXPECT_FALSE(AssertionCovered(afail));
  EXPECT_GT(AssertAttemptCovered(afail), 0U);
  EXPECT_EQ(AssertSuccessCovered(afail), 0U);
  EXPECT_GT(AssertFailureCovered(afail), 0U);

  // apass: attempted, succeeds on each attempt.
  AssertionCoverageCounters apass;
  apass.attempts = 5;
  apass.successes = 5;
  EXPECT_TRUE(AssertionCovered(apass));
  EXPECT_GT(AssertAttemptCovered(apass), 0U);
  EXPECT_GT(AssertSuccessCovered(apass), 0U);
  EXPECT_EQ(AssertFailureCovered(apass), 0U);
}

// C10: in-progress attempts derive from attempts minus all concluded outcomes.
TEST(CoverageInformationQueries,
     InProgressDerivesFromAttemptsMinusConclusions) {
  AssertionCoverageCounters c;
  c.attempts = 10;
  c.successes = 3;
  c.vacuous_successes = 1;
  c.disabled = 1;
  c.killed = 1;
  c.failures = 2;
  // 10 - (3 + 1 + 1 + 1 + 2) = 2 still in progress.
  const std::optional<std::uint64_t> kInProgress = AssertInProgress(c);
  ASSERT_TRUE(kInProgress.has_value());
  EXPECT_EQ(*kInProgress, 2U);

  AssertionCoverageCounters all_concluded;
  all_concluded.attempts = 4;
  all_concluded.successes = 4;
  const std::optional<std::uint64_t> kNone = AssertInProgress(all_concluded);
  ASSERT_TRUE(kNone.has_value());
  EXPECT_EQ(*kNone, 0U);
}

// C10 (edge): the derivation never reports a negative figure. Should the
// recorded outcomes ever exceed the attempt count the in-progress total is
// clamped to zero rather than wrapping around.
TEST(CoverageInformationQueries, InProgressClampsWhenOutcomesExceedAttempts) {
  AssertionCoverageCounters c;
  c.attempts = 2;
  c.successes = 3;  // more recorded conclusions than counted attempts
  c.failures = 2;
  const std::optional<std::uint64_t> kInProgress = AssertInProgress(c);
  ASSERT_TRUE(kInProgress.has_value());
  EXPECT_EQ(*kInProgress, 0U);
}

// C11: the in-progress identity does not apply to cover sequences.
TEST(CoverageInformationQueries, InProgressUndefinedForCoverSequence) {
  AssertionCoverageCounters seq;
  seq.is_cover_sequence = true;
  seq.attempts = 3;
  seq.successes = 7;  // more matches than attempts is legitimate here
  EXPECT_FALSE(AssertInProgress(seq).has_value());
}

// C2: vpiCovered on a multi-entity handle reports how many entities are covered
// (statements, FSM states, or individual signal bits).
TEST(CoverageInformationQueries, CoveredEntityCountReportsCoveredEntities) {
  EntityCoverage e;
  e.total = 8;
  e.covered = 5;
  EXPECT_EQ(CoveredEntityCount(e), 5U);
}

// C13: vpiCoveredCount reports how many times an item has been covered.
TEST(CoverageInformationQueries, CoveredCountReportsHitCount) {
  EntityCoverage e;
  e.total = 8;
  e.covered = 5;
  e.hit_count = 42;
  EXPECT_EQ(CoveredCount(e), 42U);
}

// C1: vpi_get(<coverageType>, instance_handle) selects the covered-item count
// for the requested coverage type within the instance.
TEST(CoverageInformationQueries, InstanceCoverageSelectsByCoverageType) {
  InstanceCoverage inst;
  inst.assertions.covered = 1;
  inst.fsm_states.covered = 2;
  inst.statements.covered = 3;
  inst.toggles.covered = 4;

  EXPECT_EQ(InstanceCoverageCount(CoverageProperty::kAssertCoverage, inst), 1U);
  EXPECT_EQ(InstanceCoverageCount(CoverageProperty::kFsmStateCoverage, inst),
            2U);
  EXPECT_EQ(InstanceCoverageCount(CoverageProperty::kStatementCoverage, inst),
            3U);
  EXPECT_EQ(InstanceCoverageCount(CoverageProperty::kToggleCoverage, inst), 4U);
  // A property that is not a coverage type selects nothing.
  EXPECT_EQ(InstanceCoverageCount(CoverageProperty::kCovered, inst), 0U);
}

}  // namespace
}  // namespace delta
