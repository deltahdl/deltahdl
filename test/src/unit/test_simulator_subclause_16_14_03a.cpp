// Tests for IEEE 1800-2023 §16.14.3 "Cover statement".
//
// This subclause has no grammar of its own; the cover_property_statement and
// cover_sequence_statement productions belong to §16.14. What §16.14.3 defines
// is the runtime behavior of the two cover categories: how a single evaluation
// attempt updates the coverage tallies and how often the optional pass
// statement runs. Each test observes a production helper applying one of those
// rules.

#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "common/types.h"
#include "simulator/cover_statement.h"

using namespace delta;

namespace {

// §16.14.3: the two cover categories are distinct — property coverage and
// sequence coverage are not the same thing.
TEST(CoverStatement, PropertyAndSequenceAreDistinctCategories) {
  EXPECT_NE(CoverStatementCategory::kProperty,
            CoverStatementCategory::kSequence);
}

// §16.14.3: for a cover property the attempt counter includes the attempts that
// result in a disabled evaluation.
TEST(CoverStatement, PropertyAttemptCounterIncludesDisabledEvaluations) {
  CoverPropertyAttemptOutcome disabled;
  disabled.disabled = true;
  EXPECT_EQ(CoverPropertyAttemptDelta(disabled), 1U);

  CoverPropertyAttemptOutcome ordinary;
  EXPECT_EQ(CoverPropertyAttemptDelta(ordinary), 1U);
}

// §16.14.3: the success and vacuous-success counters do not include disabled
// evaluations.
TEST(CoverStatement, PropertySuccessCountersExcludeDisabledEvaluations) {
  CoverPropertyAttemptOutcome disabled_success;
  disabled_success.disabled = true;
  disabled_success.nonvacuous_success = true;
  EXPECT_EQ(CoverPropertySuccessDelta(disabled_success), 0U);

  CoverPropertyAttemptOutcome disabled_vacuous;
  disabled_vacuous.disabled = true;
  disabled_vacuous.vacuous_success = true;
  EXPECT_EQ(CoverPropertyVacuousSuccessDelta(disabled_vacuous), 0U);
}

// §16.14.3: for property coverage the count is incremented at most once per
// evaluation attempt — a nonvacuous success contributes exactly one, a vacuous
// success contributes one to the vacuity count, and a nonsuccess contributes
// none.
TEST(CoverStatement, PropertyCountIncrementsAtMostOncePerAttempt) {
  CoverPropertyAttemptOutcome nonvacuous;
  nonvacuous.nonvacuous_success = true;
  EXPECT_EQ(CoverPropertySuccessDelta(nonvacuous), 1U);
  EXPECT_EQ(CoverPropertyVacuousSuccessDelta(nonvacuous), 0U);

  CoverPropertyAttemptOutcome vacuous;
  vacuous.vacuous_success = true;
  EXPECT_EQ(CoverPropertySuccessDelta(vacuous), 0U);
  EXPECT_EQ(CoverPropertyVacuousSuccessDelta(vacuous), 1U);

  CoverPropertyAttemptOutcome nonsuccess;
  EXPECT_EQ(CoverPropertySuccessDelta(nonsuccess), 0U);
  EXPECT_EQ(CoverPropertyVacuousSuccessDelta(nonsuccess), 0U);
}

// §16.14.3: the pass statement of a cover property runs once for each
// successful evaluation attempt of the underlying property_spec; a disabled
// evaluation is not a success and runs nothing.
TEST(CoverStatement, PropertyPassStatementRunsOncePerSuccess) {
  CoverPropertyAttemptOutcome nonvacuous;
  nonvacuous.nonvacuous_success = true;
  EXPECT_EQ(CoverPropertyPassExecutions(nonvacuous), 1U);

  CoverPropertyAttemptOutcome vacuous;
  vacuous.vacuous_success = true;
  EXPECT_EQ(CoverPropertyPassExecutions(vacuous), 1U);

  CoverPropertyAttemptOutcome nonsuccess;
  EXPECT_EQ(CoverPropertyPassExecutions(nonsuccess), 0U);

  CoverPropertyAttemptOutcome disabled;
  disabled.disabled = true;
  disabled.nonvacuous_success = true;
  EXPECT_EQ(CoverPropertyPassExecutions(disabled), 0U);
}

// §16.14.3: the results of coverage for a sequence include the number of times
// attempted — each evaluation attempt of the cover sequence increments the
// attempt counter once.
TEST(CoverStatement, SequenceAttemptCounterCountsEachAttempt) {
  EXPECT_EQ(CoverSequenceAttemptDelta(), 1U);
}

// §16.14.3: in a cover sequence, a completed match counts toward the attempt
// total only when it completes without the disable iff condition having
// occurred.
TEST(CoverStatement, SequenceMatchCountsOnlyWithoutDisableIff) {
  EXPECT_TRUE(CoverSequenceMatchCounts(/*disable_iff_occurred=*/false));
  EXPECT_FALSE(CoverSequenceMatchCounts(/*disable_iff_occurred=*/true));
}

// §16.14.3: for sequence coverage all matches per attempt are reported — every
// match that completes without disable iff is counted with multiplicity, and no
// other match contributes to the total.
TEST(CoverStatement, SequenceCountsEveryMatchWithMultiplicity) {
  // Three matches complete in this attempt; the second saw the disable iff
  // condition occur, so only the first and third are counted.
  std::vector<bool> matches = {false, true, false};
  EXPECT_EQ(CoverSequenceMatchDelta(matches), 2U);

  // An attempt with no completed match counts nothing.
  EXPECT_EQ(CoverSequenceMatchDelta({}), 0U);

  // Multiplicity: four clean matches all count.
  EXPECT_EQ(CoverSequenceMatchDelta({false, false, false, false}), 4U);
}

// §16.14.3: the pass statement of a cover sequence runs, with multiplicity,
// once for each match counted toward the attempt total.
TEST(CoverStatement, SequencePassStatementRunsPerCountedMatch) {
  std::vector<bool> matches = {false, true, false};
  EXPECT_EQ(CoverSequencePassExecutions(matches), 2U);
  EXPECT_EQ(CoverSequencePassExecutions({false, false, false}), 3U);
}

// §16.14.3 (edge): no match other than one completing without the disable iff
// condition is counted. When every completed match in an attempt occurred under
// the disable iff condition, the attempt contributes zero matches and its pass
// statement runs zero times.
TEST(CoverStatement, SequenceExcludesAllMatchesUnderDisableIff) {
  std::vector<bool> all_under_disable_iff = {true, true, true};
  EXPECT_EQ(CoverSequenceMatchDelta(all_under_disable_iff), 0U);
  EXPECT_EQ(CoverSequencePassExecutions(all_under_disable_iff), 0U);
}

// §16.14.3: the pass statement of either cover category executes in the
// Reactive region of the time step in which the attempt succeeds or the match
// completes.
TEST(CoverStatement, PassStatementExecutesInReactiveRegion) {
  EXPECT_EQ(CoverPassStatementRegion(), Region::kReactive);
}

}  // namespace
