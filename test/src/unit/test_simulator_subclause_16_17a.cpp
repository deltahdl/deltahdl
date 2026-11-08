#include <gtest/gtest.h>

#include "common/types.h"
#include "simulator/sva_engine_queues.h"
#include "simulator/sva_engine_sequences.h"

using namespace delta;

namespace {

TEST(ExpectStatement, PendingKeepsProcessBlocked) {
  EXPECT_EQ(ResolveExpectAction(PropertyResult::kPending, true),
            ExpectActionKind::kBlock);
  EXPECT_TRUE(ExpectProcessRemainsBlocked(PropertyResult::kPending));
}

TEST(ExpectStatement, SuccessTakesPassArm) {
  EXPECT_EQ(ResolveExpectAction(PropertyResult::kPass, true),
            ExpectActionKind::kRunPass);
  EXPECT_EQ(ResolveExpectAction(PropertyResult::kVacuousPass, false),
            ExpectActionKind::kRunPass);
  EXPECT_FALSE(ExpectProcessRemainsBlocked(PropertyResult::kPass));
}

TEST(ExpectStatement, PendingBlocksRegardlessOfElseClause) {
  EXPECT_EQ(ResolveExpectAction(PropertyResult::kPending, false),
            ExpectActionKind::kBlock);
  EXPECT_EQ(ResolveExpectAction(PropertyResult::kPending, true),
            ExpectActionKind::kBlock);
}

TEST(ExpectStatement, VacuousPassUnblocksProcess) {
  EXPECT_FALSE(ExpectProcessRemainsBlocked(PropertyResult::kVacuousPass));
}

TEST(ExpectStatement, FailureWithElseTakesElseArm) {
  EXPECT_EQ(ResolveExpectAction(PropertyResult::kFail, true),
            ExpectActionKind::kRunFail);
  EXPECT_FALSE(ExpectProcessRemainsBlocked(PropertyResult::kFail));
}

TEST(ExpectStatement, FailureWithoutElseReportsViaError) {
  EXPECT_EQ(ResolveExpectAction(PropertyResult::kFail, false),
            ExpectActionKind::kReportError);
  EXPECT_EQ(ExpectDefaultFailSeverity(), AssertionSeverity::kError);
}

TEST(ExpectStatement, FirstEvaluationOnNextClockingEvent) {
  EXPECT_FALSE(ExpectClockingEventBeginsEvaluation(10, 9));
  EXPECT_FALSE(ExpectClockingEventBeginsEvaluation(10, 10));
  EXPECT_TRUE(ExpectClockingEventBeginsEvaluation(10, 11));
}

TEST(ExpectStatement, ResumesAfterObservedInReactiveRegion) {
  EXPECT_EQ(ExpectResumeRegion(), Region::kReactive);
}

}  // namespace
