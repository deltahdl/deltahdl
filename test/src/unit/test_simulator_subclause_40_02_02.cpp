#include <gtest/gtest.h>

#include "helpers_fsm_pragma_lexing.h"
#include "simulator/vpi_coverage.h"

using namespace delta;

namespace {

// §40.2.2 "Nomenclature" defines the three coverage terms the rest of clause 40
// is written in. Assertion coverage is "for each assertion, whether it has had
// at least one success", with implementations permitting "querying for further
// details, such as attempt counts, success counts, failure counts". FSM
// coverage is "the number of states in an FSM that this simulation reached",
// and the standard "does not require FSM automatic extraction, but a standard
// mechanism to force specific extraction is available via pragmas". Statement
// coverage is "whether a statement has been executed", where "covered means it
// executed at least once", with the execution count queryable and the
// granularity "per-statement or per-statement block depending on the query".
// These tests read each term back out of what answers for it.

// §40.2.2, assertion coverage: whether the assertion has had a success. One
// that succeeded is covered, one that was attempted and never succeeded is not,
// and the further details the term allows for - how many attempts, successes
// and failures there were - are each a number of their own.
TEST(CoverageNomenclature, AssertionCoverageIsWhetherItHasSucceeded) {
  AssertionCoverageCounters succeeded;
  succeeded.attempts = 4;
  succeeded.successes = 2;

  AssertionCoverageCounters never_succeeded;
  never_succeeded.attempts = 4;
  never_succeeded.vacuous_successes = 4;

  EXPECT_TRUE(AssertionCovered(succeeded));
  EXPECT_FALSE(AssertionCovered(never_succeeded));

  // The further details: attempt, success and failure counts.
  EXPECT_EQ(AssertAttemptCovered(succeeded), 4u);
  EXPECT_EQ(AssertSuccessCovered(succeeded), 2u);
  EXPECT_EQ(AssertFailureCovered(succeeded), 0u);
}

// §40.2.2, FSM coverage: a number of states rather than a yes or no. An FSM
// whose simulation reached three of its five states reports three covered out
// of five coverable, which is what makes a coverage percentage of an FSM mean
// anything.
TEST(CoverageNomenclature, FsmCoverageCountsTheStatesReached) {
  EntityCoverage fsm;
  fsm.total = 5;
  fsm.covered = 3;

  EXPECT_EQ(CoveredEntityCount(fsm), 3u);
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kAggregate, fsm), 5u);

  // One state of that machine is a single coverable entity, whatever the
  // machine around it holds.
  EntityCoverage one_state;
  one_state.total = 5;
  one_state.covered = 1;
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kFsmState, one_state), 1u);
}

// §40.2.2, FSM coverage, the other half of the term: the standard requires no
// automatic extraction, and what it does define is the pragma a source writes
// to force a specific extraction. That pragma is read where a comment would
// otherwise be discarded.
TEST(CoverageNomenclature, FsmExtractionIsForcedByThePragma) {
  auto pragmas =
      CollectFsmPragmas("/* tool state_vector cur_state enum state_e */");

  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signal, "cur_state");
  EXPECT_TRUE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[0].enum_name, "state_e");
}

// §40.2.2, statement coverage: executed at least once is what covered means, so
// a statement that ran is covered however many times it ran, one that never ran
// is not, and the execution count is a separate number for the implementations
// that report it.
TEST(CoverageNomenclature, StatementCoverageIsExecutionAtLeastOnce) {
  EntityCoverage executed;
  executed.total = 1;
  executed.covered = 1;
  executed.hit_count = 7;

  EntityCoverage never_executed;
  never_executed.total = 1;

  EXPECT_EQ(CoveredEntityCount(executed), 1u);
  EXPECT_EQ(CoveredEntityCount(never_executed), 0u);
  // Covered says it ran; the hit count says how often, and the two are not the
  // same number.
  EXPECT_EQ(CoveredCount(executed), 7u);
  EXPECT_EQ(CoveredCount(never_executed), 0u);
}

// §40.2.2, statement coverage granularity: "per-statement or per-statement
// block depending on the query". The same term answers for one statement and
// for the block that holds it - the block reports how many of its statements
// are covered, out of how many it holds, where the single statement reports
// itself alone.
TEST(CoverageNomenclature, StatementGranularityFollowsTheQuery) {
  EntityCoverage block;
  block.total = 12;
  block.covered = 9;

  EntityCoverage statement;
  statement.total = 1;
  statement.covered = 1;

  EXPECT_EQ(CoveredEntityCount(block), 9u);
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kAggregate, block), 12u);
  EXPECT_EQ(CoveredEntityCount(statement), 1u);
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kAggregate, statement), 1u);
}

}  // namespace
