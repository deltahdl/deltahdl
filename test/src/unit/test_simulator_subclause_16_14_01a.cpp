#include <gtest/gtest.h>

#include "common/types.h"
#include "simulator/sva_engine_queues.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/sva_engine_sequences.h"

using namespace delta;

namespace {

TEST(AssertStatement, ActionBlockChoiceFollowsPropertyOutcome) {
  EXPECT_EQ(SelectAssertActionBlock(true, false),
            AssertActionBlockChoice::kPass);
  EXPECT_EQ(SelectAssertActionBlock(false, false),
            AssertActionBlockChoice::kFail);
  EXPECT_EQ(SelectAssertActionBlock(false, true),
            AssertActionBlockChoice::kNone);
}

TEST(AssertStatement, DisabledTakesPrecedenceOverPass) {
  EXPECT_EQ(SelectAssertActionBlock(true, true),
            AssertActionBlockChoice::kNone);
}

TEST(AssertStatement, ActionControlSuppressesSelectedBranch) {
  EXPECT_EQ(ResolveAssertActionUnderControl(AssertActionBlockChoice::kPass,
                                            false, true),
            AssertActionBlockChoice::kNone);
  EXPECT_EQ(ResolveAssertActionUnderControl(AssertActionBlockChoice::kFail,
                                            true, false),
            AssertActionBlockChoice::kNone);
  EXPECT_EQ(ResolveAssertActionUnderControl(AssertActionBlockChoice::kFail,
                                            true, true),
            AssertActionBlockChoice::kFail);
}

TEST(AssertStatement, DefaultErrorOnFailureUnlessSuppressed) {
  DeferredAssertion da;
  da.condition_val = 0;
  da.has_else_clause = false;
  EXPECT_TRUE(CallsDefaultErrorOnFailure(da, true));
  EXPECT_FALSE(CallsDefaultErrorOnFailure(da, false));
}

TEST(AssertStatement, NoDefaultErrorWhenElseClausePresent) {
  DeferredAssertion da;
  da.condition_val = 0;
  da.has_else_clause = true;
  EXPECT_FALSE(CallsDefaultErrorOnFailure(da, true));
}

TEST(AssertStatement, DefaultSeverityIsError) {
  EXPECT_EQ(DefaultConcurrentAssertActionSeverity(), AssertionSeverity::kError);
}

TEST(AssertStatement, ActionExecutesInReactiveRegion) {
  EXPECT_EQ(ConcurrentAssertActionRegion(), Region::kReactive);
}

TEST(AssertStatement, ControlAllowsPassBranchWhenEnabled) {
  EXPECT_EQ(ResolveAssertActionUnderControl(AssertActionBlockChoice::kPass,
                                            true, true),
            AssertActionBlockChoice::kPass);
}

TEST(AssertStatement, ControlDoesNotResurrectDisabledAction) {
  EXPECT_EQ(ResolveAssertActionUnderControl(AssertActionBlockChoice::kNone,
                                            true, true),
            AssertActionBlockChoice::kNone);
}

TEST(AssertStatement, NoDefaultErrorWhenPropertyPasses) {
  DeferredAssertion da;
  da.condition_val = 1;
  da.has_else_clause = false;
  EXPECT_FALSE(CallsDefaultErrorOnFailure(da, true));
}

TEST(AssertStatement, NoDefaultErrorForCover) {
  DeferredAssertion da;
  da.condition_val = 0;
  da.has_else_clause = false;
  da.kind = AssertionKind::kCover;
  EXPECT_FALSE(CallsDefaultErrorOnFailure(da, true));
}

}  // namespace
