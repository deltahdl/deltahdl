#include <gtest/gtest.h>

#include <vector>

#include "common/types.h"
#include "simulator/cover_statement.h"

using namespace delta;

namespace {

TEST(CoverStatement, PropertyAndSequenceAreDistinctCategories) {
  EXPECT_NE(CoverStatementCategory::kProperty,
            CoverStatementCategory::kSequence);
}

TEST(CoverStatement, PropertyAttemptCounterIncludesDisabledEvaluations) {
  CoverPropertyAttemptOutcome disabled;
  disabled.disabled = true;
  EXPECT_EQ(CoverPropertyAttemptDelta(disabled), 1U);

  CoverPropertyAttemptOutcome ordinary;
  EXPECT_EQ(CoverPropertyAttemptDelta(ordinary), 1U);
}

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

TEST(CoverStatement, SequenceAttemptCounterCountsEachAttempt) {
  EXPECT_EQ(CoverSequenceAttemptDelta(), 1U);
}

TEST(CoverStatement, SequenceMatchCountsOnlyWithoutDisableIff) {
  EXPECT_TRUE(CoverSequenceMatchCounts(false));
  EXPECT_FALSE(CoverSequenceMatchCounts(true));
}

TEST(CoverStatement, SequenceCountsEveryMatchWithMultiplicity) {
  std::vector<bool> matches = {false, true, false};
  EXPECT_EQ(CoverSequenceMatchDelta(matches), 2U);

  EXPECT_EQ(CoverSequenceMatchDelta({}), 0U);

  EXPECT_EQ(CoverSequenceMatchDelta({false, false, false, false}), 4U);
}

TEST(CoverStatement, SequencePassStatementRunsPerCountedMatch) {
  std::vector<bool> matches = {false, true, false};
  EXPECT_EQ(CoverSequencePassExecutions(matches), 2U);
  EXPECT_EQ(CoverSequencePassExecutions({false, false, false}), 3U);
}

TEST(CoverStatement, SequenceExcludesAllMatchesUnderDisableIff) {
  std::vector<bool> all_under_disable_iff = {true, true, true};
  EXPECT_EQ(CoverSequenceMatchDelta(all_under_disable_iff), 0U);
  EXPECT_EQ(CoverSequencePassExecutions(all_under_disable_iff), 0U);
}

TEST(CoverStatement, PassStatementExecutesInReactiveRegion) {
  EXPECT_EQ(CoverPassStatementRegion(), Region::kReactive);
}

}  // namespace
