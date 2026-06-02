#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.17: the expect statement blocks the executing process until the property
// succeeds or fails. While the evaluation is pending the process stays blocked.
TEST(ExpectStatement, PendingKeepsProcessBlocked) {
  EXPECT_EQ(ResolveExpectAction(PropertyResult::kPending, /*has_else=*/true),
            ExpectActionKind::kBlock);
  EXPECT_TRUE(ExpectProcessRemainsBlocked(PropertyResult::kPending));
}

// §16.17: if the property succeeds, the optional pass statement of the action
// block is executed and the process unblocks.
TEST(ExpectStatement, SuccessTakesPassArm) {
  EXPECT_EQ(ResolveExpectAction(PropertyResult::kPass, /*has_else=*/true),
            ExpectActionKind::kRunPass);
  EXPECT_EQ(ResolveExpectAction(PropertyResult::kVacuousPass, /*has_else=*/false),
            ExpectActionKind::kRunPass);
  EXPECT_FALSE(ExpectProcessRemainsBlocked(PropertyResult::kPass));
}

// §16.17: the process blocks until the property succeeds or fails. While the
// outcome is still pending, the action block is never entered and the process
// keeps waiting — independent of whether an else clause is present, since the
// arm is only chosen once the property resolves.
TEST(ExpectStatement, PendingBlocksRegardlessOfElseClause) {
  EXPECT_EQ(ResolveExpectAction(PropertyResult::kPending, /*has_else=*/false),
            ExpectActionKind::kBlock);
  EXPECT_EQ(ResolveExpectAction(PropertyResult::kPending, /*has_else=*/true),
            ExpectActionKind::kBlock);
}

// §16.17: success unblocks the process and runs the pass arm. A vacuous pass is
// a success, so it likewise unblocks the process rather than keeping it waiting.
TEST(ExpectStatement, VacuousPassUnblocksProcess) {
  EXPECT_FALSE(ExpectProcessRemainsBlocked(PropertyResult::kVacuousPass));
}

// §16.17: if the property fails at its clocking event, the optional else clause
// of the action block is executed.
TEST(ExpectStatement, FailureWithElseTakesElseArm) {
  EXPECT_EQ(ResolveExpectAction(PropertyResult::kFail, /*has_else=*/true),
            ExpectActionKind::kRunFail);
  EXPECT_FALSE(ExpectProcessRemainsBlocked(PropertyResult::kFail));
}

// §16.17: if the else clause is omitted, the tool reports the failure by
// calling $error — i.e. at error severity.
TEST(ExpectStatement, FailureWithoutElseReportsViaError) {
  EXPECT_EQ(ResolveExpectAction(PropertyResult::kFail, /*has_else=*/false),
            ExpectActionKind::kReportError);
  EXPECT_EQ(ExpectDefaultFailSeverity(), AssertionSeverity::kError);
}

// §16.17: the first evaluation shall take place on the next clocking event, not
// on one coincident with the tick at which the expect was activated, and never
// on a clocking event that precedes activation.
TEST(ExpectStatement, FirstEvaluationOnNextClockingEvent) {
  EXPECT_FALSE(ExpectClockingEventBeginsEvaluation(/*activation=*/10,
                                                   /*clocking_event=*/9));
  EXPECT_FALSE(ExpectClockingEventBeginsEvaluation(/*activation=*/10,
                                                   /*clocking_event=*/10));
  EXPECT_TRUE(ExpectClockingEventBeginsEvaluation(/*activation=*/10,
                                                  /*clocking_event=*/11));
}

// §16.17: the statement following the expect is scheduled after the Observed
// region in which the property completes its evaluation — the Reactive region.
TEST(ExpectStatement, ResumesAfterObservedInReactiveRegion) {
  EXPECT_EQ(ExpectResumeRegion(), Region::kReactive);
}

}
